Stranger
========
Stranger is an Automata-Based Symbolic String Analysis Library. You can use stranger to solve string constraints and/or compute pre and post-images of string manipulation operations such as concatenation and replacement. It can handle complex regular-expression based replace operations such as PHP's preg_replace and approximate these operations in the presence of unbounded loops with high precision and smooth performance. It can also be used to do automatic repair for such bugs. Stranger stands for STRing AutomatoN GEneratoR.

Usage
=====
Stranger is a library which means that you need to statically or dynamically link to it.

You need to download and install MONA library from (http://www.brics.dk/mona/index.html). After installing MONA make sure you copy the header files bdd\_external.h and bdd\_dump.h to /usr/local/include/mona in addition to other MONA header files there.

After that, Stranger is already an Eclipse CDT project (and Mac OS X XCode project if you prefer) and you can use Eclipse CDT to build it (Eclipse IDE for C and C++ is available from http://www.eclipse.org/downloads/packages/eclipse-ide-cc-developers/keplersr1).

The output of the compilation will be a dynamic library called libstrangerlib.so (or libstrangerlib.dylib on Mac OS X). You need to include stranger.h in your program and link your program against Stranger and MONA. If you need to get more involved with stranger you may need to include stranger\_lib\_internal.h and/or MONA header files.

Read documentation in [stranger.h](stranger.h) to get an idea of Stranger library interface and the different functions that can be called. You can look at [test.c](test.c) for examples on how to use stranger to analyze C and PHP programs.
