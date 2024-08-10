## Process this file with automake to produce Makefile.in

lib_LTLIBRARIES = libginacsym.la
libginacsym_la_SOURCES = add.cpp archive.cpp basic.cpp clifford.cpp color.cpp \
    constant.cpp ex.cpp expair.cpp expairseq.cpp exprseq.cpp \
    fail.cpp factor.cpp fderivative.cpp function.cpp idx.cpp indexed.cpp inifcns.cpp \
    inifcns_trans.cpp inifcns_gamma.cpp inifcns_nstdsums.cpp inifcns_elliptic.cpp integration_kernel.cpp \
    integral.cpp lst.cpp matrix.cpp mul.cpp ncmul.cpp normal.cpp numeric.cpp \
    operators.cpp power.cpp registrar.cpp relational.cpp remember.cpp \
    pseries.cpp print.cpp symbol.cpp symmetry.cpp tensor.cpp \
    utils.cpp wildcard.cpp \
    remember.h utils.h crc32.h hash_seed.h \
    utils_multi_iterator.h \
ginacwrapper.cpp\
infinity.cpp \
functions.cpp \
inifcns_trig.cpp \
inifcns_hyperb.cpp \
inifcns_special.cpp \
inifcns_integral.cpp \
inert.cpp \
integrate.cpp \
map_function.cpp \
outform.cpp \
simplify.cpp \
solve.cpp \
utility.cpp \
limit.cpp \
number.cpp \
poly_algebra.cpp \
    parser/parse_binop_rhs.cpp \
    parser/parser.cpp \
    parser/parse_context.cpp \
    parser/default_reader.cpp \
    parser/lexer.cpp \
    parser/lexer.h \
    parser/parser_compat.cpp \
    parser/debug.h \
    polynomial/mod_gcd.cpp \
    polynomial/cra_garner.cpp \
    polynomial/gcd_euclid.h \
    polynomial/remainder.cpp \
    polynomial/remainder.h \
    polynomial/normalize.cpp \
    polynomial/normalize.h \
    polynomial/upoly.h \
    polynomial/ring_traits.h \
    polynomial/mod_gcd.h \
    polynomial/cra_garner.h \
    polynomial/upoly_io.h \
    polynomial/upoly_io.cpp \
    polynomial/prem_uvar.h \
    polynomial/eval_uvar.h \
    polynomial/interpolate_padic_uvar.h \
    polynomial/sr_gcd_uvar.h \
    polynomial/heur_gcd_uvar.h \
    polynomial/gcd_uvar.cpp \
    polynomial/chinrem_gcd.cpp \
    polynomial/chinrem_gcd.h \
    polynomial/collect_vargs.cpp \
    polynomial/collect_vargs.h \
    polynomial/divide_in_z_p.cpp \
    polynomial/divide_in_z_p.h \
    polynomial/euclid_gcd_wrap.h \
    polynomial/eval_point_finder.h \
    polynomial/mgcd.cpp \
    polynomial/newton_interpolate.h \
    polynomial/optimal_vars_finder.cpp \
    polynomial/optimal_vars_finder.h \
    polynomial/pgcd.cpp \
    polynomial/pgcd.h \
    polynomial/poly_cra.h \
    polynomial/primes_factory.h \
    polynomial/primpart_content.cpp \
    polynomial/smod_helpers.h \
    polynomial/debug.h

libginacsym_la_LDFLAGS = -version-info @LT_VERSION_INFO@
libginacsym_la_CPPFLAGS = -DLIBEXECDIR='"$(libexecdir)/"'
libginacsym_la_LIBADD = $(DL_LIBS)
#AM_CFLAGS = $(DEPENDENCIES_CFLAGS)
#LDADD = $(DEPENDENCIES_LIBS)
ginacsymincludedir = $(includedir)/ginacsym
ginacsyminclude_HEADERS = ginacsym.h add.h archive.h assertion.h basic.h class_info.h \
    clifford.h color.h constant.h container.h ex.h expair.h expairseq.h \
    exprseq.h fail.h factor.h fderivative.h flags.h function.h hash_map.h idx.h indexed.h \
    inifcns.h integration_kernel.h integral.h lst.h matrix.h mul.h ncmul.h normal.h numeric.h operators.h \
    power.h print.h pseries.h ptr.h registrar.h relational.h structure.h \
    symbol.h symmetry.h tensor.h version.h wildcard.h compiler.h utils.h \
    ginacwrapper.h \
    infinity.h\
    functions.h \
    inert.h \
    integrate.h \
    outform.h \
    simplify.h \
    solve.h \
    utility.h \
    limit.h \
    number.h \
    poly_algebra.h \
    parser.h \
    parse_context.h

