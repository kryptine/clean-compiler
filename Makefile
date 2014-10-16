ROOT=$(shell pwd)
BACKEND_CSF=$(ROOT)/backend/Clean\ System\ Files
BACKEND_LIBRARY_SOURCE=$(ROOT)/backendC/CleanCompilerSources/backend.a
BACKEND_LIBRARY_TARGET=$(BACKEND_CSF)/backend_library
TONIC_DIR=$(ROOT)/frontend/Tonic

default: $(BACKEND_LIBRARY_TARGET)
	cpm project CleanCompilerMacOSX.prj build
	cp cocl ~/clean/lib/exe/cocl-tonic
	cp cocl ~/clean/exe/cocl-tonic

force: $(BACKEND_LIBRARY_TARGET)
	cpm project CleanCompilerMacOSX.prj build --force
	cp cocl ~/clean/lib/exe/cocl-tonic
	cp cocl ~/clean/exe/cocl-tonic

$(BACKEND_CSF):
	mkdir -p $(BACKEND_CSF)

$(BACKEND_LIBRARY_TARGET): $(BACKEND_CSF) $(BACKEND_LIBRARY_SOURCE)
	ln -sf $(BACKEND_LIBRARY_SOURCE) $(BACKEND_LIBRARY_TARGET)

$(BACKEND_LIBRARY_SOURCE): $(ROOT)/backendC/CleanCompilerSources/Makefile.linux64
	cd backendC/CleanCompilerSources && make -f Makefile.linux64
	cd main/Unix && make -f Makefile all

$(BACKEND_LIBRARY_SOURCE): $(ROOT)/backendC/CleanCompilerSources/Makefile.linux64
	cd backendC/CleanCompilerSources && make -f Makefile.linux64
	cd main/Unix && make -f Makefile all

$(TONIC_AG_ICL): $(TONIC_AG_FILE) $(TONIC_DIR)/ExprSyn.ag $(TONIC_DIR)/Pretty.ag $(TONIC_DIR)/MkGraph.ag
	uuagc --kennedywarren --clean -cfwmH $(TONIC_AG_FILE)
