#!/bin/sh
CLM=clm

(cd backendC/CleanCompilerSources; make)
(cd ../libraries/ArgEnvUnix; make ArgEnvC.o)
(cd main/Unix; make -f Makefile all);
$CLM -ci -I backend -I frontend -I main -I main/Unix -ABC -fusion backendconvert
$CLM -h 24M -nt -nw -ci -ns -nr -I backend -I frontend -I main -I main/Unix \
	-I ../libraries/ArgEnvUnix \
	-l backendC/CleanCompilerSources/backend.a \
	cocl -o cocl
#	-l ../libraries/ArgEnvUnix/ArgEnvC.o \
#	-l main/Unix/cDirectory.o \
#	-l main/Unix/set_return_code_c.o \
#	-l main/Unix/ipc.o \
