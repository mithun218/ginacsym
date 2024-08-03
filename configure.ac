#!/bin/sh
dnl Set version info.
dnl ginacsym release number:
dnl    m4_define([ginacsym_major_version], [1])
dnl    m4_define([ginacsym_minor_version], [0])
dnl    m4_define([ginacsym_micro_version], [0])
dnl    m4_define([ginacsym_version], [ginacsym_major_version.ginacsym_minor_version.ginacsym_micro_version])
dnl    m4_define([ginacsym_release], [ginacsym_major_version.ginacsym_minor_version])
dnl    dnl ginacsym library version information. It has very little to do with ginacsym
dnl    dnl version number. In particular, library version is OS dependent.
dnl    m4_define([ginacsym_lt_current], [m4_eval(ginacsym_major_version + ginacsym_minor_version)])
dnl    m4_define([ginacsym_lt_age], [ginacsym_minor_version]))
dnl    m4_define([ginacsym_lt_revision], [ginacsym_micro_version]))
m4_define([ginacsym_major_version], GINACSYM_GET_VERSION([MAJOR]))
m4_define([ginacsym_minor_version], GINACSYM_GET_VERSION([MINOR]))
m4_define([ginacsym_micro_version], GINACSYM_GET_VERSION([MICRO]))
m4_define([ginacsym_version], [ginacsym_major_version.ginacsym_minor_version.ginacsym_micro_version])
m4_define([ginacsym_release], [ginacsym_major_version.ginacsym_minor_version])
dnl GiNaC library version information. It has very little to do with GiNaC
dnl version number. In particular, library version is OS dependent.
m4_define([ginacsym_lt_current], GINACSYM_GET_LTVERSION([CURRENT]))
m4_define([ginacsym_lt_age], GINACSYM_GET_LTVERSION([AGE]))
m4_define([ginacsym_lt_revision], GINACSYM_GET_LTVERSION([REVISION]))

AC_INIT([ginacSym], [ginacsym_version], [ginacsym-list@ginacsym.in], [ginacsym], [https://www.ginacsym.in/])
AC_PREREQ([2.59])
AC_CONFIG_SRCDIR(ginacsym/basic.cpp)
AC_CONFIG_AUX_DIR([config])
AC_CONFIG_HEADERS([config/config.h])
AC_CONFIG_MACRO_DIR([m4])

dnl AC_CHECK_HEADERS([],[],[],[#DEFINE IN_GINACSYM])

dnl This defines PACKAGE and VERSION.
AM_INIT_AUTOMAKE([gnu 1.8 dist-bzip2 subdir-objects])

dnl libtool versioning
LT_VERSION_INFO="ginacsym_lt_current:ginacsym_lt_revision:ginacsym_lt_age"
AC_SUBST(LT_VERSION_INFO)

dnl Check for the compiler and all the utilities needed for the build.
AC_PROG_CXX
AC_PROG_CXXCPP
AC_PROG_INSTALL
LT_INIT

dnl Switch to C++ language mode for the following libraries and headers.
AC_LANG([C++])
AX_CXX_COMPILE_STDCXX([11])

# Checks for programs.
AC_PROG_CC

# Checks for libraries.
# CAUTION: Order matters for static binary building.
dnl    AC_SEARCH_LIBS([atan2],[m],
dnl        [],
dnl        [AC_MSG_ERROR(["The C math library was not found!"])])

dnl    AC_SEARCH_LIBS([__gmpz_init],[gmp],
dnl        [],
dnl        [AC_MSG_ERROR(["GMP library was not found."])])

dnl    AC_SEARCH_LIBS([mpfr_init],[mpfr],
dnl        [],
dnl        [AC_MSG_ERROR([MPFR library was not found.])])

dnl    AC_SEARCH_LIBS([fmpz_add_ui],[flint],
dnl        [],
dnl        [AC_MSG_ERROR([FLINT library was not found.])])

PKG_CHECK_MODULES([DEPENDENCIES], [flint >= 3 cln >= 1.3.4])
CPPFLAGS="$CPPFLAGS $DEPENDENCIES_CFLAGS"
LIBS="$LIBS $DEPENDENCIES_LIBS"
dnl        AC_SUBST([DEPENDENCIES_CFLAGS])
dnl        AC_SUBST([DEPENDENCIES_LIBS])

dnl We need to have CLN installed.
dnl    PKG_CHECK_MODULES(GMP, gmp >= 1.2.2)
dnl        AC_SUBST([GMP_CFLAGS])
dnl        AC_SUBST([GMP_LIBS])
dnl    AC_LIB_LINKFLAGS_FROM_LIBS([CLN_RPATH], [$CLN_LIBS])
dnl    LIBS="$LIBS $GMP_LIBS"
dnl    CPPFLAGS="$CPPFLAGS $GMP_CFLAGS"

dnl We need to have CLN installed.
dnl    PKG_CHECK_MODULES(MPFR, mpfr >= 1.2.2)
dnl        AC_SUBST([MPFR_CFLAGS])
dnl        AC_SUBST([MPFR_LIBS])
dnl    AC_LIB_LINKFLAGS_FROM_LIBS([CLN_RPATH], [$CLN_LIBS])
dnl    LIBS="$LIBS $MPFR_LIBS"
dnl    CPPFLAGS="$CPPFLAGS $MPFR_CFLAGS"

dnl We need to have CLN installed.
dnl    PKG_CHECK_MODULES(FLINT, flint >= 1.2.2)
dnl        AC_SUBST([FLINT_CFLAGS])
dnl        AC_SUBST([FLINT_LIBS])
dnl    AC_LIB_LINKFLAGS_FROM_LIBS([CLN_RPATH], [$CLN_LIBS])
dnl    LIBS="$LIBS $FLINT_LIBS"
dnl    CPPFLAGS="$CPPFLAGS $FLINT_CFLAGS"

dnl We need to have CLN installed.
dnl    PKG_CHECK_MODULES(CLN, cln >= 1.2.2)
dnl        AC_SUBST([CLN_CFLAGS])
dnl        AC_SUBST([CLN_LIBS])
dnl    AC_LIB_LINKFLAGS_FROM_LIBS([CLN_RPATH], [$CLN_LIBS])
dnl    LIBS="$LIBS $CLN_LIBS"
dnl    CPPFLAGS="$CPPFLAGS $CLN_CFLAGS"

GINACSYMLIB_LIBS='-L${libdir} -lginacsym'
AC_LIB_LINKFLAGS_FROM_LIBS([GINACSYMLIB_RPATH], [$GINACSYMLIB_LIBS])


dnl Output makefiles etc.
AC_CONFIG_FILES([
Makefile
ginacsym.pc
ginacsym/Makefile
check/Makefile
])
AC_OUTPUT

dnl Display a final warning if there has been a GINACSYM_ERROR or a GINACSYM_WARNING
GINACSYM_CHECK_ERRORS
