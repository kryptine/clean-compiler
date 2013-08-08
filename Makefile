BACKEND_CSF=backend/Clean\ System\ Files
BACKEND_LIBRARY_SOURCE=backendC/CleanCompilerSources/backend.a
BACKEND_LIBRARY_TARGET=$(BACKEND_CSF)/backend_library

default: frontend/tonic.icl $(BACKEND_LIBRARY)
	cpm project CleanCompilerMacOSX.prj build
	cp cocl ~/clean/exe/itasks/cocl-tonic

$(BACKEND_CSF):
	mkdir -p $(BACKEND_CSF)

$(BACKEND_LIBRARY): $(BACKEND_CSF) $(BACKEND_LIBRARY_SOURCE)
	ln -s $(BACKEND_LIBRARY_SOURCE) $(BACKEND_LIBRARY_TARGET)

$(BACKEND_LIBRARY_SOURCE): backendC/CleanCompilerSources/Makefile.linux64
	cd backendC/CleanCompilerSources & make -f Makefile.linux64
	cd main/Unix & make -f Makefile all

frontend/tonic.icl: frontend/tonic.ag
	uuagc --kennedywarren --clean -cfswH frontend/tonic.ag

