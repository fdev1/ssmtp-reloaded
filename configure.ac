dnl Process this file with autoconf to produce a configure script.
AC_INIT([sSMTP-Reloaded], [0.9.5], [https://github.com/fernando-rodriguez/ssmtp-reloaded/issues])
AC_CONFIG_SRCDIR(ssmtp.c)

dnl Checks for programs.
AC_PROG_CC
AC_PROG_INSTALL
AC_PROG_LN_S
AC_PROG_SED
AC_PATH_PROG([GROUPADD], [groupadd])

dnl Checks for libraries.

dnl Checks for header files.
AC_CHECK_HEADERS(syslog.h)

dnl Checks for libraries.
AC_SEARCH_LIBS(gethostname, nsl)
AC_SEARCH_LIBS(socket, socket)

dnl Checks for library functions.
AC_CHECK_FUNCS(strndup)

dnl Check for optional features
AC_ARG_ENABLE(logfile, 
[  --enable-logfile        additional logging over and above syslog])
if test x$enableval = xyes ; then
	AC_DEFINE(LOGFILE)
fi
enableval=""

AC_ARG_ENABLE(rewrite-domain,
[  --disable-rewrite-domain
                          support for rewriting the sending domain])
if test x$enableval != xno ; then
	AC_DEFINE(REWRITE_DOMAIN)
fi
enableval=""

AC_ARG_ENABLE(ssl,
[  --enable-ssl           support for secure connection to mail server])
AC_ARG_WITH([gnutls],
  AS_HELP_STRING([--with-gnutls], [Use GnuTLS for SSL support]))
if test x$enable_ssl = "xyes" ; then
       	AC_DEFINE(HAVE_SSL)
        if test "x$with_gnutls" != "xyes"; then
        	LIBS="$LIBS -lssl -lcrypto"
        else
                AC_DEFINE([HAVE_GNUTLS])
                LIBS="$LIBS -lgnutls-openssl"
        fi
fi

AC_ARG_ENABLE(inet6,
[  --enable-inet6         support for IPv6 transport])
if test x$enableval = xyes ; then
	AC_DEFINE(INET6)
fi
enableval=""

if test x$enable_ssl = xyes ; then
	if test x$with_gnutls = xyes ; then
		AC_SEARCH_LIBS([MD5_Init], [gnutls-openssl], ,
			SRCS="$SRCS md5.c")
	else
		AC_SEARCH_LIBS([MD5_Init], [crypto], ,
			SRCS="$SRCS md5.c")
	fi
else
	SRCS="$SRCS md5.c"
fi

AC_SUBST(SRCS)

AC_CONFIG_FILES(Makefile)
AC_OUTPUT
