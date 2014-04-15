LibStranger
========
LibStranger is an Automata-Based Symbolic String Analysis Library. You can use LibStranger 
to solve string constraints and/or compute pre and post-images of string manipulation 
operations such as concatenation and replacement. It can handle complex regular-expression 
based replace operations such as PHP's preg_replace and approximate these operations in 
the presence of unbounded loops with high precision and smooth performance. It can also be
used to do automatic repair for such bugs. LibStranger stands for STRing AutomatoN GEneratoR 
Library.

Installation
============
LibStranger is a library which means that you need to statically or dynamically link to it.

You need to download and install [MONA library](http://www.brics.dk/mona/index.html). 

```bash
$> tar -xzvf mona-1.4-15.tar.gz
$> cd mona-1.4
$> ./configure
$> make
$> sudo make install
```

After installing MONA make sure you copy the header files bdd\_external.h and bdd\_dump.h to 
/usr/local/include/mona in addition to other MONA header files there.

```bash
$> cd mona-1.4
$> sudo cp BDD/bdd_external.h /usr/local/include/mona
$> sudo cp BDD/bdd_dump.h /usr/local/include/mona
```

After that, clone LibStranger to your machine (or download the automatic zip file provided 
by github) 
```bash
$> mkdir LibStranger
$> cd LibStranger
$> git clone git@github.com:vlab-cs-ucsb/LibStranger.git .
$> chmod u+x autogen.sh
$> ./autogen.sh 
```
The last step will create the GNU autotools files (i.e., configure script and makefiles) 
from the two manually written files, configure.ac and makefile.am.

Then we use the normal autotools installation system:
```bash
$> ./configure
$> make
$> sudo make install
```
The output of the compilation will be a dynamic library called libstranger.so (or 
libstranger.dylib on Mac OS X). You need to include stranger.h in your program and link 
your program against LibStranger and MONA. If you need to get more involved with 
LibStranger you may need to include stranger\_lib\_internal.h and/or MONA header files.

Test & Usage
============
You can run the testprogram to test stranger library. Here is how to compile and
run this program:
```bash
$> cd testprogram
$> gcc test_stranger.c -o test_stranger -l monabdd -l monadfa -l monamem -l stranger
$> sudo ldconfig
$> ./test_stranger
```
If you get a MONA invariant violation error message in make_basic.c then edit 
the mona file DFA/makebasic.c.
```c
#define MAX_EXCEPTION 50   /* change this to 2000. You can use a number as large number as you want */
#define MAX_VARIABLES 10   /* change this to 20. You can use 30 if you want. */
```

Read documentation in [stranger.h](src/stranger.h) to get an idea of LibStranger 
library interface and the different functions that can be called. You can look at 
[test_stranger.c](testprogram/test_stranger.c) for examples on how to use LibStranger to analyze C and PHP 
programs.
