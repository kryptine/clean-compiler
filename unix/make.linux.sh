#!/bin/sh
CLM=clm

(cd backendC/CleanCompilerSources; make)
(cd ArgEnvUnix; make ArgEnvC.o)
(cd main/Unix; make -f Makefile.linux all);
$CLM -h 20M -nt -nw -ci -ns -nr -I ArgEnvUnix -I backend -I compiler -I main -I main/Unix -I WrapDebug \
	-l ArgEnvUnix/ArgEnvC.o \
	-l main/Unix/cDirectory.o \
	-l main/Unix/set_return_code_c.o \
	-l main/Unix/ipc.o \
	-l backendC/CleanCompilerSources/backend.a \
	cocl -o cocl
