#! /usr/bin/make -f

# $Id$

COCL = cocl
#COCLFLAGS = -lat
SYS = Clean\ System\ Files

MODULES = basic pretty pfun graph dnc rule trd rewr complete history spine trace absmodule spine strat loop law

ABC = $(patsubst %,$(SYS)/%.abc,$(MODULES))

#default: $(SYS)/history.abc $(SYS)/spine.abc $(SYS)/absmodule.abc $(SYS)/trace.abc $(SYS)/complete.abc $(SYS)/rewr.abc $(SYS)/trd.abc $(SYS)/rule.abc $(SYS)/dnc.abc $(SYS)/graph.abc $(SYS)/pfun.abc $(SYS)/pretty.abc $(SYS)/basic.abc
default: $(ABC)

clean:
	rm -Rf errors.err $(SYS)

%: $(SYS)/%.abc
	@:

$(SYS)/%.abc: %.icl
	$(COCL) $(COCLFLAGS) $*

$(SYS)/law.abc: law.icl law.dcl
$(SYS)/loop.abc: loop.icl loop.dcl trace.dcl strat.dcl history.dcl rule.dcl graph.dcl basic.dcl
$(SYS)/strat.abc: strat.icl strat.dcl history.dcl spine.dcl dnc.dcl rule.dcl graph.dcl pfun.dcl basic.dcl
$(SYS)/history.abc: history.icl history.dcl spine.dcl rule.dcl graph.dcl basic.dcl
$(SYS)/spine.abc: spine.icl spine.dcl rule.dcl pfun.dcl basic.dcl
$(SYS)/absmodule.abc: absmodule.icl absmodule.dcl rule.dcl
$(SYS)/trace.abc: trace.icl trace.dcl rule.dcl
$(SYS)/complete.abc: complete.icl complete.dcl graph.dcl
$(SYS)/rewr.abc: rewr.icl rewr.dcl graph.dcl pfun.dcl basic.dcl
$(SYS)/trd.abc: trd.icl trd.dcl rule.dcl graph.dcl basic.dcl
$(SYS)/rule.abc: rule.icl rule.dcl graph.dcl basic.dcl
$(SYS)/dnc.abc: dnc.icl dnc.dcl graph.dcl
$(SYS)/graph.abc: graph.icl graph.dcl pfun.dcl basic.dcl
$(SYS)/pfun.abc: pfun.icl pfun.dcl basic.dcl
$(SYS)/pretty.abc: pretty.icl pretty.dcl
$(SYS)/basic.abc: basic.icl basic.dcl
