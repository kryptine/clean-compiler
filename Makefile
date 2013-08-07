default: frontend/tonic.icl
	#cd backendC/CleanCompilerSources & make -f Makefile.linux64
	#cd main/Unix & make -f Makefile all
	#cpm project CleanCompilerMacOSX.prj build
	./unix/make.macosx64-platform.sh && cp cocl ~/clean/exe/itasks/cocl-tonic

frontend/tonic.icl: frontend/tonic.ag
	uuagc --kennedywarren --clean -cfswH frontend/tonic.ag

