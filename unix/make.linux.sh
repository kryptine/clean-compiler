#!/bin/sh
CLM=clm

(cd backendC/CleanCompilerSources; make)
(cd ../libraries/ArgEnvUnix; make ArgEnvC.o)
(cd main/Unix; CFLAGS=-m32 make -f Makefile all);
$CLM -ci -I backend -I frontend -I main -I main/Unix -ABC -fusion backendconvert
$CLM -h 40M -nt -nw -ci -nr -I backend -I frontend -I main -I main/Unix \
	-IL ArgEnv \
	-l backendC/CleanCompilerSources/backend.a \
	-l -m32 \
	cocl -o cocl
