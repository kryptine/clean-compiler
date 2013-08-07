#!/bin/sh
CLM=clm

(cd backendC/CleanCompilerSources; make -f Makefile.linux64)
(cd main/Unix; make -f Makefile all);
$CLM -gcm -h 512m -s 128m -nt -nw -ci -nr -IL ArgEnv -IL Dynamics -I backend -I frontend -I main -I main/Unix \
    -I ~/clean/clean-platform-flat/OS-Independent \
    -I ~/clean/clean-platform-flat/OS-Independent/Control \
    -I ~/clean/clean-platform-flat/OS-Independent/Control/Monad \
    -I ~/clean/clean-platform-flat/OS-Independent/Data \
    -I ~/clean/clean-platform-flat/OS-Independent/Text \
    -l backendC/CleanCompilerSources/backend.a \
    cocl -o cocl
