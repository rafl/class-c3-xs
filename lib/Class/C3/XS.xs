
#include "EXTERN.h"
#include "perl.h"
#include "XSUB.h"
 
STATIC I32
__dopoptosub_at(const PERL_CONTEXT *cxstk, I32 startingblock) {
    I32 i;
    for (i = startingblock; i >= 0; i--) {
	register const PERL_CONTEXT * const cx = &cxstk[i];
	switch (CxTYPE(cx)) {
	default:
	    continue;
	case CXt_EVAL:
	case CXt_SUB:
	case CXt_FORMAT:
	    DEBUG_l( Perl_deb(aTHX_ "(Found sub #%ld)\n", (long)i));
	    return i;
	}
    }
    return i;
}

MODULE = Class::C3::XS	PACKAGE = next

#ifdef XXX_NEW_PERL /* some sort of cpp check for a perl that has mro_linear */

/* we want to define next::can, next::method, and maybe::next::method */

CV*
canxs(self)
    SV* self
  PPCODE:
    register I32 cxix = __dopoptosub_at(cxstack, cxstack_ix);
    register const PERL_CONTEXT *cx;
    register const PERL_CONTEXT *ccstack = cxstack;
    const PERL_SI *top_si = PL_curstackinfo;
    HV* selfstash;
    //sv_dump(self);
    if(sv_isobject(self)) {
        selfstash = SvSTASH(SvRV(self));
    }
    else {
        selfstash = gv_stashsv(self, 0);
    }
    assert(selfstash);

    for (;;) {
        /* we may be in a higher stacklevel, so dig down deeper */
        while (cxix < 0 && top_si->si_type != PERLSI_MAIN) {
            top_si = top_si->si_prev;
            ccstack = top_si->si_cxstack;
            cxix = __dopoptosub_at(ccstack, top_si->si_cxix);
        }
        if (cxix < 0) {
            croak("next::/maybe::next:: must be used in method context");
        }
    
        /* caller() should not report the automatic calls to &DB::sub */
        if (PL_DBsub && GvCV(PL_DBsub) && cxix >= 0 && ccstack[cxix].blk_sub.cv == GvCV(PL_DBsub))
            continue;

        cx = &ccstack[cxix];
        if (CxTYPE(cx) == CXt_SUB || CxTYPE(cx) == CXt_FORMAT) {
            const I32 dbcxix = __dopoptosub_at(ccstack, cxix - 1);
            /* We expect that ccstack[dbcxix] is CXt_SUB, anyway, the
               field below is defined for any cx. */
            /* caller() should not report the automatic calls to &DB::sub */
            if (PL_DBsub && GvCV(PL_DBsub) && dbcxix >= 0 && ccstack[dbcxix].blk_sub.cv == GvCV(PL_DBsub))
                cx = &ccstack[dbcxix];
            }
            if (CxTYPE(cx) == CXt_SUB || CxTYPE(cx) == CXt_FORMAT) {
	        GV * const cvgv = CvGV(ccstack[cxix].blk_sub.cv);
	        /* So is ccstack[dbcxix]. */
	        if (isGV(cvgv)) { /* we found a real sub here */
                    const char *stashname;
                    const char *fq_subname;
                    const char *subname;
                    STRLEN fq_subname_len;
                    STRLEN stashname_len;
                    STRLEN subname_len;
                    GV * found_gv;
	            SV * const sv = sv_2mortal(newSV(0));

	            gv_efullname3(sv, cvgv, NULL);

                    fq_subname = SvPVX(sv);
                    fq_subname_len = SvCUR(sv);
/*                    warn("fqsubname is %s", fq_subname); */
                    
                    subname = strrchr(fq_subname, ':');
                    if(subname) {
                        subname++;
                        subname_len = fq_subname_len - (subname - fq_subname);
                        stashname = fq_subname;
                        stashname_len = subname - fq_subname - 2;
                        if(subname_len == 8 && strEQ(subname, "__ANON__")) {
                            croak("Cannot use next::method/next::can/maybe::next::method from an anonymous sub");
                        }
                        else {
                            GV** gvp;
                            AV* linear_av;
                            SV** linear_svp;
                            SV* linear_sv;
                            HV* curstash;
                            GV* candidate = NULL;
                            CV* cand_cv = NULL;
                            const char *hvname;
                            I32 items;

                            hvname = HvNAME_get(selfstash);
                            if (!hvname)
                              Perl_croak(aTHX_ "Can't use anonymous symbol table for method lookup");

                            linear_av = mro_linear(selfstash); /* has ourselves at the top of the list */
                            sv_2mortal((SV*)linear_av);

                            linear_svp = AvARRAY(linear_av) + 1; /* skip over self */
                            items = AvFILLp(linear_av); /* no +1, to skip over self */

                            while (items--) {
                                linear_sv = *linear_svp++;
                                assert(linear_sv);
                                if(strEQ(SvPVX(linear_sv), stashname)) break;
                            }

                            while (items--) {
                                linear_sv = *linear_svp++;
                                assert(linear_sv);
                                curstash = gv_stashsv(linear_sv, FALSE);

                                if (!curstash) {
                                    if (ckWARN(WARN_MISC))
                                        Perl_warner(aTHX_ packWARN(WARN_MISC), "Can't locate package %"SVf" for @%s::ISA",
                                            (void*)linear_sv, hvname);
                                    continue;
                                }

                                assert(curstash);

                                gvp = (GV**)hv_fetch(curstash, subname, subname_len, 0);
                                if (!gvp) continue;
                                candidate = *gvp;
                                assert(candidate);
                                if (SvTYPE(candidate) != SVt_PVGV) gv_init(candidate, curstash, subname, subname_len, TRUE);
                                if (SvTYPE(candidate) == SVt_PVGV && (cand_cv = GvCV(candidate)) && !GvCVGEN(candidate)) {
                                    PUSHs((SV*)cand_cv);
                                    return;
                                }
                            }
    
                            /* Check UNIVERSAL without caching */
                            if((candidate = gv_fetchmeth(NULL, subname, subname_len, 1))) {
                                PUSHs((SV*)GvCV(candidate));
                                return;
                            }
                            PUSHs(&PL_sv_undef);
                            return;
                        }
                    }
	        }
            }

	    cxix = __dopoptosub_at(ccstack, cxix - 1);
        }


#else /* mro_linear stuff not in core, so do some helpers for the pure-perl variant */

/* we want to define two helper functions:
   1) A replacement for Alg::C3::merge based on mro_linear_c3, but without the mro_meta caching parts.
      it should have optional merge cache support just like Alg::C3 does, but only support @ISA, not
      generic parents.  Call it Class::C3::calculateMRO_XS or something.
   2) A fast "fetch the most recent caller's package/sub-names", based on the xs can function above,
      to speed up the top half of pure-perl next::method.
*/
#endif
