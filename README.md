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

After that, run 
```bash
$> 
$> chmod u+x autogen.sh
$> ./autogen.sh 
```
to create the GNU autotools files.
Then run
```bash
./configure
make
make install
```
The output of the compilation will be a dynamic library called libstranger.so (or libstranger.dylib on Mac OS X). You need to include stranger.h in your program and link your program against LibStranger and MONA. If you need to get more involved with LibStranger you may need to include stranger\_lib\_internal.h and/or MONA header files.

Test & Usage
============
Read documentation in [stranger.h](stranger.h) to get an idea of LibStranger library interface and the different functions that can be called. You can look at [test.c](test.c) for examples on how to use LibStranger to analyze C and PHP programs.
