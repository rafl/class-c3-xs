
#include "EXTERN.h"
#include "perl.h"
#include "XSUB.h"

/* Most of this code is backported from the bleadperl patch's
   mro.c, and then modified to work with Class::C3's
   internals.
*/

AV*
__mro_linear_isa_c3(pTHX_ HV* stash, HV* cache, I32 level)
{
    AV* retval;
    GV** gvp;
    GV* gv;
    AV* isa;
    const char* stashname;
    STRLEN stashname_len;

    assert(stash);
    assert(HvAUX(stash));

    stashname = HvNAME(stash);
    stashname_len = strlen(stashname);
    if (!stashname)
      Perl_croak(aTHX_
                 "Can't linearize anonymous symbol table");

    if (level > 100)
        Perl_croak(aTHX_ "Recursive inheritance detected in package '%s'",
              stashname);

    if(!cache) {
        cache = (HV*)sv_2mortal((SV*)newHV());
    }
    else {
        sv_dump(cache);
        SV** cache_entry = hv_fetch(cache, stashname, stashname_len, 0);
        if(cache_entry)
            return (AV*)SvREFCNT_inc(*cache_entry);
    }

    /* not in cache, make a new one */

    retval = (AV*)sv_2mortal((SV*)newAV());
    av_push(retval, newSVpvn(stashname, stashname_len)); /* us first */

    gvp = (GV**)hv_fetch(stash, "ISA", 3, FALSE);
    isa = (gvp && (gv = *gvp) && gv != (GV*)&PL_sv_undef) ? GvAV(gv) : NULL;

    if(isa && AvFILLp(isa) >= 0) {
        SV** seqs_ptr;
        I32 seqs_items;
        HV* tails = (HV*)sv_2mortal((SV*)newHV());
        AV* seqs = (AV*)sv_2mortal((SV*)newAV());
        I32 items = AvFILLp(isa) + 1;
        SV** isa_ptr = AvARRAY(isa);
        while(items--) {
            AV* isa_lin;
            SV* isa_item = *isa_ptr++;
            HV* isa_item_stash = gv_stashsv(isa_item, 0);
            if(!isa_item_stash) {
                isa_lin = newAV();
                av_push(isa_lin, newSVsv(isa_item));
            }
            else {
                isa_lin = (AV*)sv_2mortal((SV*)__mro_linear_isa_c3(isa_item_stash, cache, level + 1)); /* recursion */
            }
            av_push(seqs, (SV*)av_make(AvFILLp(isa_lin)+1, AvARRAY(isa_lin)));
        }
        av_push(seqs, (SV*)av_make(AvFILLp(isa)+1, AvARRAY(isa)));

        seqs_ptr = AvARRAY(seqs);
        seqs_items = AvFILLp(seqs) + 1;
        while(seqs_items--) {
            AV* seq = (AV*)*seqs_ptr++;
            I32 seq_items = AvFILLp(seq);
            if(seq_items > 0) {
                SV** seq_ptr = AvARRAY(seq) + 1;
                while(seq_items--) {
                    SV* seqitem = *seq_ptr++;
                    HE* he = hv_fetch_ent(tails, seqitem, 0, 0);
                    if(!he) {
                        hv_store_ent(tails, seqitem, newSViv(1), 0);
                    }
                    else {
                        SV* val = HeVAL(he);
                        sv_inc(val);
                    }
                }
            }
        }

        while(1) {
            SV* seqhead = NULL;
            SV* cand = NULL;
            SV* winner = NULL;
            SV* val;
            HE* tail_entry;
            AV* seq;
            SV** avptr = AvARRAY(seqs);
            items = AvFILLp(seqs)+1;
            while(items--) {
                SV** svp;
                seq = (AV*)*avptr++;
                if(AvFILLp(seq) < 0) continue;
                svp = av_fetch(seq, 0, 0);
                seqhead = *svp;
                if(!winner) {
                    cand = seqhead;
                    if((tail_entry = hv_fetch_ent(tails, cand, 0, 0))
                       && (val = HeVAL(tail_entry))
                       && (SvIVx(val) > 0))
                           continue;
                    winner = newSVsv(cand);
                    av_push(retval, winner);
                }
                if(!sv_cmp(seqhead, winner)) {

                    /* this is basically shift(@seq) in void context */
                    SvREFCNT_dec(*AvARRAY(seq));
                    *AvARRAY(seq) = &PL_sv_undef;
                    AvARRAY(seq) = AvARRAY(seq) + 1;
                    AvMAX(seq)--;
                    AvFILLp(seq)--;

                    if(AvFILLp(seq) < 0) continue;
                    svp = av_fetch(seq, 0, 0);
                    seqhead = *svp;
                    tail_entry = hv_fetch_ent(tails, seqhead, 0, 0);
                    val = HeVAL(tail_entry);
                    sv_dec(val);
                }
            }
            if(!cand) break;
            if(!winner)
                Perl_croak(aTHX_ "Inconsistent hierarchy during C3 merge of class '%s': "
                    "merging failed on parent '%s'", stashname, SvPV_nolen(cand));
        }
    }

    SvREADONLY_on(retval);
    SvREFCNT_inc(retval); /* for cache storage */
    SvREFCNT_inc(retval); /* for return */
    hv_store(cache, stashname, stashname_len, (SV*)retval, 0);
    return retval;
}

STATIC I32
__dopoptosub_at(const PERL_CONTEXT *cxstk, I32 startingblock) {
    I32 i;
    for (i = startingblock; i >= 0; i--) {
        if(CxTYPE((PERL_CONTEXT*)(&cxstk[i])) == CXt_SUB) return i;
    }
    return i;
}

STATIC SV*
__nextcan(pTHX_ SV* self, I32 throw_nomethod)
{
    register I32 cxix;
    register const PERL_CONTEXT *ccstack = cxstack;
    const PERL_SI *top_si = PL_curstackinfo;
    HV* selfstash;
    GV* cvgv;
    SV *stashname;
    const char *fq_subname;
    const char *subname;
    STRLEN fq_subname_len;
    STRLEN stashname_len;
    STRLEN subname_len;
    SV* sv;
    GV** gvp;
    AV* linear_av;
    SV** linear_svp;
    SV* linear_sv;
    HV* cstash;
    GV* candidate = NULL;
    CV* cand_cv = NULL;
    const char *hvname;
    I32 items;
    struct mro_meta* selfmeta;
    HV* nmcache;
    HE* cache_entry;

    if(sv_isobject(self))
        selfstash = SvSTASH(SvRV(self));
    else
        selfstash = gv_stashsv(self, 0);

    assert(selfstash);

    hvname = HvNAME(selfstash);
    if (!hvname)
        croak("Can't use anonymous symbol table for method lookup");

    cxix = __dopoptosub_at(cxstack, cxstack_ix);

    /* This block finds the contextually-enclosing fully-qualified subname,
       much like looking at (caller($i))[3] until you find a real sub that
       isn't ANON, etc */
    for (;;) {
        /* we may be in a higher stacklevel, so dig down deeper */
        while (cxix < 0) {
            if(top_si->si_type == PERLSI_MAIN)
                croak("next::method/next::can/maybe::next::method must be used in method context");
            top_si = top_si->si_prev;
            ccstack = top_si->si_cxstack;
            cxix = __dopoptosub_at(ccstack, top_si->si_cxix);
        }

        if(CxTYPE((PERL_CONTEXT*)(&ccstack[cxix])) != CXt_SUB
          || (PL_DBsub && GvCV(PL_DBsub) && ccstack[cxix].blk_sub.cv == GvCV(PL_DBsub))) {
            cxix = __dopoptosub_at(ccstack, cxix - 1);
            continue;
        }

        {
            const I32 dbcxix = __dopoptosub_at(ccstack, cxix - 1);
            if (PL_DBsub && GvCV(PL_DBsub) && dbcxix >= 0 && ccstack[dbcxix].blk_sub.cv == GvCV(PL_DBsub)) {
                if(CxTYPE((PERL_CONTEXT*)(&ccstack[dbcxix])) != CXt_SUB) {
                    cxix = dbcxix;
                    continue;
                }
            }
        }

        cvgv = CvGV(ccstack[cxix].blk_sub.cv);

        if(!isGV(cvgv)) {
            cxix = __dopoptosub_at(ccstack, cxix - 1);
            continue;
        }

        /* we found a real sub here */
        sv = sv_2mortal(newSV(0));

        gv_efullname3(sv, cvgv, NULL);

        fq_subname = SvPVX(sv);
        fq_subname_len = SvCUR(sv);

        subname = strrchr(fq_subname, ':');
        if(!subname)
            croak("next::method/next::can/maybe::next::method cannot find enclosing method");

        subname++;
        subname_len = fq_subname_len - (subname - fq_subname);
        if(subname_len == 8 && strEQ(subname, "__ANON__")) {
            cxix = __dopoptosub_at(ccstack, cxix - 1);
            continue;
        }
        break;
    }

    /* If we made it to here, we found our context */

    /* 
    XXX check %next::METHOD_CACHE 

    selfmeta = HvMROMETA(selfstash);
    if(!(nmcache = selfmeta->mro_nextmethod)) {
        nmcache = selfmeta->mro_nextmethod = newHV();
    }

    if((cache_entry = hv_fetch_ent(nmcache, sv, 0, 0))) {
        SV* val = HeVAL(cache_entry);
        if(val == &PL_sv_undef) {
            if(throw_nomethod)
                croak("No next::method '%s' found for %s", subname, hvname);
            return &PL_sv_undef;
        }
        return SvREFCNT_inc(val);
    }
    */

    /* beyond here is just for cache misses, so perf isn't as critical */

    stashname_len = subname - fq_subname - 2;
    stashname = sv_2mortal(newSVpvn(fq_subname, stashname_len));

    linear_av = (AV*)sv_2mortal((SV*)__mro_linear_isa_c3(selfstash, NULL, 0));

    linear_svp = AvARRAY(linear_av);
    items = AvFILLp(linear_av) + 1;

    while (items--) {
        linear_sv = *linear_svp++;
        assert(linear_sv);
        if(sv_eq(linear_sv, stashname))
            break;
    }

    if(items > 0) {
        SV* sub_sv = sv_2mortal(newSVpv(subname, subname_len));
        HV* cc3_mro = get_hv("Class::C3::MRO", 0);

        while (items--) {
            linear_sv = *linear_svp++;
            assert(linear_sv);

            if(cc3_mro) {
                HE* he_cc3_mro_class = hv_fetch_ent(cc3_mro, linear_sv, 0, 0);
                if(he_cc3_mro_class) {
                    HV* cc3_mro_class = (HV*)SvRV(HeVAL(he_cc3_mro_class));
                    SV** svp_cc3_mro_class_methods = hv_fetch(cc3_mro_class, "methods", 7, 0);
                    if(svp_cc3_mro_class_methods) {
                        HV* cc3_mro_class_methods = (HV*)SvRV(*svp_cc3_mro_class_methods);
                        if(hv_exists_ent(cc3_mro_class_methods, sub_sv, 0))
                            continue;
                    }
                }
            }

            cstash = gv_stashsv(linear_sv, FALSE);

            if (!cstash) {
                if (ckWARN(WARN_MISC))
                    Perl_warner(aTHX_ packWARN(WARN_MISC), "Can't locate package %"SVf" for @%s::ISA",
                        (void*)linear_sv, hvname);
                continue;
            }

            assert(cstash);

            gvp = (GV**)hv_fetch(cstash, subname, subname_len, 0);
            if (!gvp) continue;

            candidate = *gvp;
            assert(candidate);

            if (SvTYPE(candidate) != SVt_PVGV)
                gv_init(candidate, cstash, subname, subname_len, TRUE);
            if (SvTYPE(candidate) == SVt_PVGV && (cand_cv = GvCV(candidate)) && !GvCVGEN(candidate)) {
                SvREFCNT_inc((SV*)cand_cv);
                /* XXX store result in cache */
                /* hv_store_ent(nmcache, newSVsv(sv), (SV*)cand_cv, 0); */
                return (SV*)cand_cv;
            }
        }
    }

    /* XXX store undef in cache */
    /* hv_store_ent(nmcache, newSVsv(sv), &PL_sv_undef, 0); */
    if(throw_nomethod)
        croak("No next::method '%s' found for %s", subname, hvname);
    return &PL_sv_undef;
}

XS(XS_Class_C3_XS_calculateMRO);
XS(XS_Class_C3_XS_calculateMRO)
{
#ifdef dVAR
    dVAR; dXSARGS;
#else
    dXSARGS;
#endif

    SV* classname;
    HV* class_stash;
    HV* cache = NULL;
    AV* res;
    I32 res_items;
    I32 ret_items;
    SV** res_ptr;

    if(items < 1 || items > 2)
        croak("Usage: calculateMRO(classname[, cache])");

    classname = ST(0);
    if(items == 2) cache = (HV*)SvRV(ST(1));

    class_stash = gv_stashsv(classname, 0);
    if(!class_stash) croak("No such class: '%s'!", SvPV_nolen(classname));

    res = (AV*)sv_2mortal((SV*)__mro_linear_isa_c3(class_stash, cache, 0));

    res_items = ret_items = AvFILLp(res) + 1;
    res_ptr = AvARRAY(res);

    SP -= items;

    while(res_items--) {
        SV* res_item = *res_ptr++;
        XPUSHs(res_item);
    }

    PUTBACK;

    return;
}

XS(XS_next_can);
XS(XS_next_can)
{
#ifdef dVAR
    dVAR; dXSARGS;
#else
    dXSARGS;
#endif

    SV* self = ST(0);
    SV* methcv = __nextcan(self, 0);

    PERL_UNUSED_VAR(items);

    if(methcv == &PL_sv_undef) {
        ST(0) = &PL_sv_undef;
    }
    else {
        ST(0) = sv_2mortal(newRV_inc(methcv));
    }

    XSRETURN(1);
}

XS(XS_next_method);
XS(XS_next_method)
{
    dMARK;
    dAX;
    SV* self = ST(0);
    SV* methcv = __nextcan(self, 1);

    PL_markstack_ptr++;
    call_sv(methcv, GIMME_V);
}

XS(XS_maybe_next_method);
XS(XS_maybe_next_method)
{
    dMARK;
    dAX;
    SV* self = ST(0);
    SV* methcv = __nextcan(self, 0);

    if(methcv == &PL_sv_undef) {
        ST(0) = &PL_sv_undef;
        XSRETURN(1);
    }

    PL_markstack_ptr++;
    call_sv(methcv, GIMME_V);
}

MODULE = Class::C3::XS	PACKAGE = Class::C3::XS

BOOT:
    newXS("Class::C3::XS::calculateMRO", XS_Class_C3_XS_calculateMRO, __FILE__);
    newXS("next::can", XS_next_can, __FILE__);
    newXS("next::method", XS_next_method, __FILE__);
    newXS("maybe::next::method", XS_maybe_next_method, __FILE__);
