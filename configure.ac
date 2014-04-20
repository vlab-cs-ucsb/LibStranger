# Process this file with autoconf to produce a configure script.

dnl ========== initialization ==========

AC_PREREQ(2.61)

# Initialize Autoconf. Specify package’s name, version number, bug-report address, tar-file name, web address 
AC_INIT([stranger],[0.1.0],[muath@cs.ucsb.edu],[libstranger],[http://www.cs.ucsb.edu/~vlab/stranger])

# safty check to make sure 'configure' is not run from outer space
AC_CONFIG_SRCDIR([src/auto_core_ops.c])

# Auxiliary scripts such as install-sh and depcomp should be in direcotry build-aux
AC_CONFIG_AUX_DIR([build-aux])

# use directory m4 for m4 output. We need this since we are building a library not
# a program
AC_CONFIG_MACRO_DIR([m4])

# Initialize Automake. Turn on all Automake warnings and report them as errors. 
# This is a foreign package (no need for INSTALL NEWS ...etc)
AM_INIT_AUTOMAKE([subdir-objects foreign -Wall])

# Initialize libtool. Declare this project as a libtool library not an executable program
LT_INIT


dnl ========== checks for programs ==========

# Check for a C compiler
AC_PROG_CC

dnl ========== checks for header files ==========

AC_HEADER_STDC
AC_HEADER_STDBOOL
AC_HEADER_ASSERT
AC_CHECK_HEADERS([limits.h]
				,[],AC_MSG_ERROR(limits.h file not found),[])
AC_CHECK_HEADERS([locale.h]
				,[],AC_MSG_ERROR(locale.h file not found),[])
AC_CHECK_HEADERS([math.h]
				,[],AC_MSG_ERROR(math.h file not found),[])
AC_CHECK_HEADERS([mona/gnuc.h mona/dfa.h mona/mem.h mona/bdd.h mona/bdd_external.h mona/bdd_dump.h] 
                 ,[],AC_MSG_ERROR(required MONA library header file not found),[])

dnl ========== checks for typedefs, structures, and compiler characteristics ==========

AC_C_CONST
AC_C_INLINE
AC_TYPE_SIZE_T

dnl ========== checks for libraries ========

AC_CHECK_LIB([monadfa], [dfaFree], [MONADFALIB=-lmonadfa], AC_MSG_ERROR(MONA DFA library not found))
# this will define a variable variable. you can use it in automake.am $(MONADFALIB)
AC_SUBST([MONADFALIB])

AC_CHECK_LIB([monabdd], [bdd_size], [MONABDDLIB=-lmonabdd], AC_MSG_ERROR(MONA BDD library not found))
AC_SUBST([MONABDDLIB])

AC_CHECK_LIB([monamem], [mem_alloc], [MONAMEMLIB=-lmonamem], AC_MSG_ERROR(MONA MEM library not found))
AC_SUBST([MONAMEMLIB])

AC_CHECK_LIB([m], [floor],[MLIB=-lm], AC_MSG_ERROR(c math library m not found))
AC_SUBST([MLIB])

dnl ========== checks for library functions ==========

AC_DEFUN([FUNCTION_MISSING], [AC_MSG_ERROR(required library function not found)])

AC_FUNC_MALLOC
AC_FUNC_MEMCMP
AC_FUNC_MMAP
AC_CHECK_FUNCS(memset localeconv,,FUNCTION_MISSING)

dnl ========== output file ==========

# Declare conﬁg.h as output header
AC_CONFIG_HEADERS([config.h])

AC_CONFIG_FILES([makefile])

AC_OUTPUT
