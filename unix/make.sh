#!/bin/sh
CLM=clm

(cd backendC/CleanCompilerSources; make)
$CLM -h 20M -nt -nw -ci -ns -I ArgEnvUnix -I backend -I compiler -I main -I main/Unix -I WrapDebug \
	-l ArgEnvUnix/ArgEnvC.o \
	-l main/Unix/cDirectory.o \
	-l main/Unix/set_return_code_c.o \
	-l main/Unix/ipc.o \
	-l backendC/CleanCompilerSources/backend.a \
	cocl -o cocl
