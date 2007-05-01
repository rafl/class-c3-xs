
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
        SV** cache_entry = hv_fetch(cache, stashname, stashname_len, 0);
        if(cache_entry)
            return (AV*)SvREFCNT_inc(*cache_entry);
    }

    /* not in cache, make a new one */

    retval = newAV();
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
                isa_lin = (AV*)sv_2mortal((SV*)__mro_linear_isa_c3(aTHX_ isa_item_stash, cache, level + 1)); /* recursion */
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
                    sv_2mortal(av_shift(seq));
                    if(AvFILLp(seq) < 0) continue;
                    svp = av_fetch(seq, 0, 0);
                    seqhead = *svp;
                    tail_entry = hv_fetch_ent(tails, seqhead, 0, 0);
                    val = HeVAL(tail_entry);
                    sv_dec(val);
                }
            }
            if(!cand) break;
            if(!winner) {
                SvREFCNT_dec(retval);
                Perl_croak(aTHX_ "Inconsistent hierarchy during C3 merge of class '%s': "
                    "merging failed on parent '%s'", stashname, SvPV_nolen(cand));
            }
        }
    }

    SvREADONLY_on(retval);
    hv_store(cache, stashname, stashname_len, (SV*)retval, 0);
    return (AV*)SvREFCNT_inc(retval);
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
    HV* nmcache;
    HE* cache_entry;
    SV* cachekey;

    if(sv_isobject(self))
        selfstash = SvSTASH(SvRV(self));
    else
        selfstash = gv_stashsv(self, 0);

    assert(selfstash);

    hvname = HvNAME(selfstash);
    if (!hvname)
        Perl_croak(aTHX_ "Can't use anonymous symbol table for method lookup");

    cxix = __dopoptosub_at(cxstack, cxstack_ix);

    /* This block finds the contextually-enclosing fully-qualified subname,
       much like looking at (caller($i))[3] until you find a real sub that
       isn't ANON, etc */
    for (;;) {
        /* we may be in a higher stacklevel, so dig down deeper */
        while (cxix < 0) {
            if(top_si->si_type == PERLSI_MAIN)
                Perl_croak(aTHX_ "next::method/next::can/maybe::next::method must be used in method context");
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
            Perl_croak(aTHX_ "next::method/next::can/maybe::next::method cannot find enclosing method");

        subname++;
        subname_len = fq_subname_len - (subname - fq_subname);
        if(subname_len == 8 && strEQ(subname, "__ANON__")) {
            cxix = __dopoptosub_at(ccstack, cxix - 1);
            continue;
        }
        break;
    }

    /* If we made it to here, we found our context */

    /* cachekey = "objpkg|context::method::name" */
    cachekey = sv_2mortal(newSVpv(hvname, 0));
    sv_catpvn(cachekey, "|", 1);
    sv_catsv(cachekey, sv);

    nmcache = get_hv("next::METHOD_CACHE", 1);
    if((cache_entry = hv_fetch_ent(nmcache, cachekey, 0, 0))) {
        SV* val = HeVAL(cache_entry);
        if(val == &PL_sv_undef) {
            if(throw_nomethod)
                Perl_croak(aTHX_ "No next::method '%s' found for %s", subname, hvname);
            return &PL_sv_undef;
        }
        return SvREFCNT_inc(val);
    }

    /* beyond here is just for cache misses, so perf isn't as critical */

    stashname_len = subname - fq_subname - 2;
    stashname = sv_2mortal(newSVpvn(fq_subname, stashname_len));

    linear_av = __mro_linear_isa_c3(aTHX_ selfstash, NULL, 0);

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
                    SV* cc3_mro_class_sv = HeVAL(he_cc3_mro_class);
                    if(SvROK(cc3_mro_class_sv)) {
                        HV* cc3_mro_class = (HV*)SvRV(cc3_mro_class_sv);
                        SV** svp_cc3_mro_class_methods = hv_fetch(cc3_mro_class, "methods", 7, 0);
                        if(svp_cc3_mro_class_methods) {
                            SV* cc3_mro_class_methods_sv = *svp_cc3_mro_class_methods;
                            if(SvROK(cc3_mro_class_methods_sv)) {
                                HV* cc3_mro_class_methods = (HV*)SvRV(cc3_mro_class_methods_sv);
                                if(hv_exists_ent(cc3_mro_class_methods, sub_sv, 0))
                                    continue;
                            }
                        }
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
                SvREFCNT_dec(linear_av);
                SvREFCNT_inc((SV*)cand_cv);
                hv_store_ent(nmcache, newSVsv(cachekey), (SV*)cand_cv, 0);
                return (SV*)cand_cv;
            }
        }
    }

    SvREFCNT_dec(linear_av);
    hv_store_ent(nmcache, newSVsv(cachekey), &PL_sv_undef, 0);
    if(throw_nomethod)
        Perl_croak(aTHX_ "No next::method '%s' found for %s", subname, hvname);
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
    if(!class_stash)
        Perl_croak(aTHX_ "No such class: '%s'!", SvPV_nolen(classname));

    res = __mro_linear_isa_c3(aTHX_ class_stash, cache, 0);

    res_items = ret_items = AvFILLp(res) + 1;
    res_ptr = AvARRAY(res);

    SP -= items;

    while(res_items--) {
        SV* res_item = *res_ptr++;
        XPUSHs(sv_2mortal(newSVsv(res_item)));
    }
    SvREFCNT_dec(res);

    PUTBACK;

    return;
}

XS(XS_Class_C3_XS_calc_mdt);
XS(XS_Class_C3_XS_calc_mdt)
{
#ifdef dVAR
    dVAR; dXSARGS;
#else
    dXSARGS;
#endif

    SV* classname;
    HV* cache;
    HV* class_stash;
    AV* class_mro;
    HV* our_c3mro; /* $Class::C3::MRO{classname} */
    SV* has_ovf;
    HV* methods;
    I32 mroitems;

    /* temps */
    HV* hv;
    HE* he;
    SV* rv;
    SV** svp;

    if(items < 1 || items > 2)
        croak("Usage: calculate_method_dispatch_table(classname[, cache])");

    classname = ST(0);
    class_stash = gv_stashsv(classname, 0);
    if(!class_stash)
        Perl_croak(aTHX_ "No such class: '%s'!", SvPV_nolen(classname));

    if(items == 2) cache = (HV*)SvRV(ST(1));

    class_mro = __mro_linear_isa_c3(aTHX_ class_stash, cache, 0);

    our_c3mro = newHV();
    hv_store(our_c3mro, "MRO", 3, (SV*)newRV_inc((SV*)class_mro), 0);

    hv = get_hv("Class::C3::MRO", 1);
    hv_store_ent(hv, classname, (SV*)newRV_noinc((SV*)our_c3mro), 0);

    methods = newHV();

    /* skip first entry */
    mroitems = AvFILLp(class_mro);
    svp = AvARRAY(class_mro) + 1;
    while(mroitems--) {
        SV* mro_class = *svp++;
        HV* mro_stash = gv_stashsv(mro_class, 0);

        if(!mro_stash) continue;

        /*if(!has_ovf) {
            SV** ovfp = hv_fetch(mro_stash, "()", 2, 0);
            if(ovfp) has_ovf = *ovfp;
        }*/

        hv_iterinit(mro_stash);
        while(he = hv_iternext(mro_stash)) {
            CV* code;
            SV* mskey;
            SV* msval = hv_iterval(mro_stash, he);
            if(SvTYPE(msval) != SVt_PVGV || !(code = GvCVu(msval)))
                continue;

            mskey = hv_iterkeysv(he);
            if(hv_exists_ent(methods, mskey, 0)) continue;
            if((he = hv_fetch_ent(class_stash, mskey, 0, 0))) {
                SV* val = HeVAL(he);
                if(val && SvTYPE(val) == SVt_PVGV && GvCVu(msval))
                    continue;
            }

            {
                HV* meth_hash = newHV();
                SV* orig = newSVsv(mro_class);
                sv_catpvn(orig, "::", 2);
                sv_catsv(orig, mskey);
                hv_store(meth_hash, "orig", 4, orig, 0);
                hv_store(meth_hash, "code", 4, newRV_inc((SV*)code), 0);
                hv_store_ent(methods, mskey, newRV_noinc((SV*)meth_hash), 0);
            }
        }
    }

    hv_store(our_c3mro, "methods", 7, newRV_noinc((SV*)methods), 0);
    hv_store(our_c3mro, "has_overload_fallback", 21, has_ovf ? SvREFCNT_inc(has_ovf) : &PL_sv_undef, 0);
    XSRETURN_EMPTY;
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
    SV* methcv = __nextcan(aTHX_ self, 0);

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
    SV* methcv = __nextcan(aTHX_ self, 1);

    PL_markstack_ptr++;
    call_sv(methcv, GIMME_V);
}

XS(XS_maybe_next_method);
XS(XS_maybe_next_method)
{
    dMARK;
    dAX;
    SV* self = ST(0);
    SV* methcv = __nextcan(aTHX_ self, 0);

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
    newXS("Class::C3::XS::_calculate_method_dispatch_table", XS_Class_C3_XS_calc_mdt, __FILE__);
    newXS("next::can", XS_next_can, __FILE__);
    newXS("next::method", XS_next_method, __FILE__);
    newXS("maybe::next::method", XS_maybe_next_method, __FILE__);

