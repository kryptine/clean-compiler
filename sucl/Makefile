#! /usr/bin/make -f

# $Id$

COCL = cocl
#COCLFLAGS = -lat
#SYS = Clean\ System\ Files
SYS = .

MODULES = cleanversion basic pfun graph dnc rule trd rewr complete history spine trace absmodule strat loop coreclean law canon cli extract newfold newtest expand convert supercompile

ABC = $(patsubst %,$(SYS)/%.abc,$(MODULES))

#default: $(SYS)/history.abc $(SYS)/spine.abc $(SYS)/absmodule.abc $(SYS)/trace.abc $(SYS)/complete.abc $(SYS)/rewr.abc $(SYS)/trd.abc $(SYS)/rule.abc $(SYS)/dnc.abc $(SYS)/graph.abc $(SYS)/pfun.abc $(SYS)/pretty.abc $(SYS)/basic.abc
default: $(ABC)

clean:
	rm -Rf errors.err $(SYS)

tags: *.dcl *.icl ../compiler/*.dcl ../compiler/*.icl
	sh cleantags $^ >$@

%: $(SYS)/%.abc
	@:

$(SYS)/%.abc: %.icl
	$(COCL) $(COCLFLAGS) $*

$(SYS)/supercompile.abc: supercompile.icl supercompile.dcl convert.dcl expand.dcl newtest.dcl cli.dcl coreclean.dcl basic.dcl
$(SYS)/convert.abc: convert.icl convert.dcl coreclean.dcl rule.dcl graph.dcl basic.dcl
$(SYS)/expand.abc: expand.icl expand.dcl newtest.dcl newfold.dcl rule.dcl rewr.dcl graph.dcl pfun.dcl basic.dcl
$(SYS)/newtest.abc: newtest.icl newtest.dcl newfold.dcl cli.dcl canon.dcl coreclean.dcl loop.dcl trace.dcl spine.dcl history.dcl complete.dcl trd.dcl rule.dcl graph.dcl basic.dcl
$(SYS)/newfold.abc: newfold.icl newfold.dcl extract.dcl trace.dcl spine.dcl history.dcl rule.dcl dnc.dcl graph.dcl basic.dcl
$(SYS)/extract.abc: extract.icl extract.dcl rule.dcl dnc.dcl graph.dcl basic.dcl
$(SYS)/cli.abc: cli.icl cli.dcl law.dcl coreclean.dcl strat.dcl absmodule.dcl rule.dcl dnc.dcl graph.dcl basic.dcl
$(SYS)/canon.abc: canon.icl canon.dcl rule.dcl graph.dcl basic.dcl
$(SYS)/law.abc: law.icl law.dcl coreclean.dcl strat.dcl spine.dcl rule.dcl dnc.dcl graph.dcl basic.dcl
$(SYS)/coreclean.abc: coreclean.icl coreclean.dcl strat.dcl spine.dcl rule.dcl graph.dcl basic.dcl
$(SYS)/loop.abc: loop.icl loop.dcl strat.dcl trace.dcl spine.dcl history.dcl rewr.dcl rule.dcl graph.dcl pfun.dcl basic.dcl
$(SYS)/strat.abc: strat.icl strat.dcl spine.dcl history.dcl rule.dcl dnc.dcl graph.dcl pfun.dcl basic.dcl
$(SYS)/absmodule.abc: absmodule.icl absmodule.dcl rule.dcl
$(SYS)/trace.abc: trace.icl trace.dcl spine.dcl history.dcl rule.dcl graph.dcl basic.dcl
$(SYS)/spine.abc: spine.icl spine.dcl history.dcl rule.dcl graph.dcl pfun.dcl basic.dcl
$(SYS)/history.abc: history.icl history.dcl rule.dcl graph.dcl pfun.dcl basic.dcl
$(SYS)/complete.abc: complete.icl complete.dcl graph.dcl
$(SYS)/rewr.abc: rewr.icl rewr.dcl rule.dcl graph.dcl pfun.dcl basic.dcl
$(SYS)/trd.abc: trd.icl trd.dcl rule.dcl graph.dcl basic.dcl
$(SYS)/rule.abc: rule.icl rule.dcl graph.dcl basic.dcl
$(SYS)/dnc.abc: dnc.icl dnc.dcl graph.dcl
$(SYS)/graph.abc: graph.icl graph.dcl pfun.dcl basic.dcl
$(SYS)/pfun.abc: pfun.icl pfun.dcl basic.dcl
#$(SYS)/pretty.abc: pretty.icl pretty.dcl
$(SYS)/basic.abc: basic.icl basic.dcl
$(SYS)/cleanversion.abc: cleanversion.icl cleanversion.dcl
