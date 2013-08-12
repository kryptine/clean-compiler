BACKEND_CSF=backend/Clean\ System\ Files
BACKEND_LIBRARY_SOURCE=backendC/CleanCompilerSources/backend.a
BACKEND_LIBRARY_TARGET=$(BACKEND_CSF)/backend_library
TONIC_AG_FILENAME=Tonic
TONIC_DIR=frontend/Tonic
TONIC_AG_FILE=$(TONIC_DIR)/$(TONIC_AG_FILENAME).ag
TONIC_AG_ICL=$(TONIC_DIR)/$(TONIC_AG_FILENAME).icl

default: $(TONIC_AG_ICL) $(BACKEND_LIBRARY)
	cpm project CleanCompilerMacOSX.prj build
	cp cocl ~/clean/exe/itasks/cocl-tonic

$(BACKEND_CSF):
	mkdir -p $(BACKEND_CSF)

$(BACKEND_LIBRARY): $(BACKEND_CSF) $(BACKEND_LIBRARY_SOURCE)
	ln -s $(BACKEND_LIBRARY_SOURCE) $(BACKEND_LIBRARY_TARGET)

$(BACKEND_LIBRARY_SOURCE): backendC/CleanCompilerSources/Makefile.linux64
	cd backendC/CleanCompilerSources & make -f Makefile.linux64
	cd main/Unix & make -f Makefile all

$(TONIC_AG_ICL): $(TONIC_AG_FILE) $(TONIC_DIR)/ExprSyn.ag $(TONIC_DIR)/Pretty.ag $(TONIC_DIR)/MkGraph.ag
	uuagc --kennedywarren --clean -cfswmH $(TONIC_AG_FILE)
