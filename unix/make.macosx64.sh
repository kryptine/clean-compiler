#!/bin/sh
CLM=clm

(cd backendC/CleanCompilerSources; make -f Makefile.linux64)
(cd ../libraries/ArgEnvUnix; make ArgEnvC.o)
(cd main/Unix; make -f Makefile all);
$CLM -gcm -h 40M -nt -nw -ci -nr -IL ArgEnv -I backend -I frontend -I main -I main/Unix \
	-l backendC/CleanCompilerSources/backend.a \
	cocl -o cocl
