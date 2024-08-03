dnl ===========================================================================
dnl Additional macros used to configure GiNaC.  We don't start our own 
dnl additions' names with AC_ but with GINACSYM_ in order to steer clear of
dnl future trouble.
dnl ===========================================================================

dnl  GINACSYM_HEADER_GETVAL(NAME,FILE)
dnl  ----------------------------
dnl  Expand at autoconf time to the value of a "#define NAME" from the given
dnl  FILE. The regexps here aren't very rugged, but are enough for us.
dnl  /dev/null as a parameter prevents a hang if $2 is accidentally omitted.
dnl  (shamelessly ripped from GMP, and changed prefix to GINACSYM_).

define(GINACSYM_HEADER_GETVAL,
[patsubst(patsubst(
esyscmd([grep "^#define $1 " $2 /dev/null 2>/dev/null]),
[^.*$1[ 	]+],[]),
[[
 	]*$],[])])
define(GINACSYM_GET_VERSION,
[GINACSYM_HEADER_GETVAL(GINACSYMLIB_$1_VERSION,[ginacsym/version.h])])
define(GINACSYM_GET_LTVERSION,
[GINACSYM_HEADER_GETVAL(GINACSYM_LT_$1,[ginacsym/version.h])])


dnl Usage: GINACSYM_ERROR(message)
dnl This macro displays the warning "message" and sets the flag ginacsym_error
dnl to yes.
AC_DEFUN([GINACSYM_ERROR],[
ginacsym_error_txt="$ginacsym_error_txt
** $1
"
ginacsym_error=yes])

dnl Usage: GINACSYM_WARNING(message)
dnl This macro displays the warning "message" and sets the flag ginacsym_warning
dnl to yes.
AC_DEFUN([GINACSYM_WARNING],[
ginacsym_warning_txt="$ginacsym_warning_txt
== $1
"
ginacsym_warning=yes])

dnl Usage: GINACSYM_CHECK_ERRORS
dnl (must be put at end of configure.in, because it exits on error)
dnl This macro displays a warning message if GINACSYM_ERROR or GINACSYM_WARNING
dnl has occured previously.
AC_DEFUN([GINACSYM_CHECK_ERRORS],[
if test "x${ginacsym_error}" = "xyes"; then
	echo
    echo "**** The following problems have been detected by configure."
    echo "**** Please check the messages below before running \"make\"."
    echo "**** (see the section 'Common Problems' in the INSTALL file)"
    echo "$ginacsym_error_txt"
    if test "x${ginacsym_warning_txt}" != "x"; then
        echo "${ginacsym_warning_txt}"
    fi
    if test "x$cache_file" != "x/dev/null"; then
        echo "deleting cache ${cache_file}"
        rm -f $cache_file
    fi
    exit 1
else 
    if test "x${ginacsym_warning}" = "xyes"; then
		echo
        echo "=== The following minor problems have been detected by configure."
        echo "=== Please check the messages below before running \"make\"."
        echo "=== (see the section 'Common Problems' in the INSTALL file)"
        echo "$ginacsym_warning_txt"
    fi
    echo "Configuration of ginacSym $VERSION done. Now type \"make\"."
fi])

AC_DEFUN([GINACSYM_HAVE_RUSAGE],
[AC_CACHE_CHECK([whether struct rusage is declared in <sys/resource.h>],
ac_cv_have_rusage,
 [AC_COMPILE_IFELSE([AC_LANG_PROGRAM([[#include <sys/times.h>
                                       #include <sys/resource.h>]],
                                     [[struct rusage resUsage;
                                       getrusage(RUSAGE_SELF, &resUsage);
                                       return 0;]])],
                    [ac_cv_have_rusage=yes],
                    [ac_cv_have_rusage=no])
])
CONFIG_RUSAGE="no"
if test "$ac_cv_have_rusage" = yes; then
  CONFIG_RUSAGE="yes"
  AC_DEFINE(HAVE_RUSAGE,,[define if struct rusage declared in <sys/resource.h>])
fi
AC_SUBST(CONFIG_RUSAGE)
])


