implementation module expand

import newtest
import newfold
import rule
import rewr
import graph
import pfun
import basic
import general
import StdEnv

mstub = stub "expand"

/*

   Expand macro rules where possible.

   The optimisation algorithm generates too many closures, many of which appear
   to be just macros that rewrite to another rule.  This module unfolds such
   macros.

   Macro rules do not have pattern matches (in pattern match representation)
   and can in principle always be unfolded.  The only catch is that they could
   be (mutually) recursive by themselves, but the optimiser must be able to
   handle that.  Being mutually recursive doesn't mean evaluation never
   terminates, as the occurrences can be at lazy positions.

   What to expand: expand (non-partial) applications of functions for which all
   of the following hold:

   [1] The function is a macro (doesn't have a pattern match aka case
       statement).

   [2] The function is not on a cycle of non-partial applications of macro
       functions.

       Exception: if there is only a single application (including partial
       applications, applications inside case functions, and exported
       functions) of the macro function, it can be expanded.

   Due to the expansion, some functions may become unused, if all their
   occurrences are unfolded.  Removal of unused functions -dead code
   elimination- is a separate matter and not handled here.

*/

/*

   Implementation.

   [1] Collect all references that could form cycles.  I.e., all non-partial
       applications of macro functions in macro function bodies.

   [2] Determine functions that are in mutually recursive groups.  It is not
       necessary to know which group.

   [3] Determine the recursive functions that have only a single reference (in
       the general sense -- requires knowledge of exported functions).

   [4] Expand all occurrences of functions with a single reference, and of all
       non-recursive functions.

*/

/*

   We only want to collect references once. However, we must make a distinction
   between references for recursive cycles (non-partial applications of macro
   functions in macro functions) versus all references.

   Therefore, we will annotate each reference with a boolean indicating if it
   can be part of a macro cycle.

   The type for a describing a function reference is `Reference'.  It is a
   product type with constructor `Reference' with three arguments.  In a
   reference

       ref = Reference recursion fromfun tofun

   `fromfun' is the name of the function that contains an application of the
   function named `tofun'.  `reference' is a boolean that is `True' iff the
   reference can play a role in cyclic macro applications.

*/

:: Reference sym = Reference Bool sym sym

showreference :: (sym->String) (Reference sym) -> String
showreference showsym (Reference cyclecand fromsym tosym)
= "(Reference "+++toString cyclecand+++" "+++showsym fromsym+++" "+++showsym tosym+++")"

expand_macros ::
    (sym->String)
    (var->String)
    [var]                               // Heap of variables for the expanded graphs
    (sym->Bool)                         // Whether the function is exported.
    [Symredresult sym var tsym tvar]    // Symbolic reduction results of all functions
 -> [Symredresult sym var tsym tvar]    // Expanded symbolic reduction results
 |  == sym
 &  == var

expand_macros showsym showvar heap exported srrs
= result
  where

        // Collect references
        // references :: [Reference sym]
        references = collect_references srrs

        // Get cyclic reference candidates
        // cycle_candidates :: [(sym,[sym])] | == sym // [(fromfun,tofuns)]
        cycle_candidates = partition fst snd [(fromfun,tofun) \\ (Reference True fromfun tofun) <- references]

        // Determine recursive functions
        // recursiveness :: [(sym,Bool)] | == sym // [(fun,recursive)]
        recursiveness = getrecursives cycle_candidates

        // Final reference count function
        reference_count sym = (if (exported sym) inc id) (foldmap length 0 references_to sym)
        references_to = partition snd fst [(fromfun,tofun) \\ (Reference _ fromfun tofun) <- references]

        // Determine which functions are expandable
        expandable sym
        = foldmap (localfn_expandable sym) False recursiveness sym
        localfn_expandable sym recursive
        = not (recursive && reference_count sym>1)
        expandable_table = map isexp recursiveness
                            where isexp (sym,recursive) = (sym,localfn_expandable sym recursive)

        result = map (expandone heap getrule) srrs
        getrule = foldmap Yes No finalruletable
        finalruletable = foldr (addexpansion expandable) [] result

addexpansion :: (sym->Bool) (Symredresult sym var tsym tvar) [(sym,Rule sym var)] -> [(sym,Rule sym var)]
addexpansion expandable srr=:{srr_assigned_symbol=sym,srr_function_def=(args,BuildGraph alt)} rest
| expandable sym
  = [(sym,mkrule args (rgraphroot alt) (rgraphgraph alt)):rest]
// Fall through
addexpansion _ _ rest = rest

/*********
GETTING REFERENCES FROM FUNCTION DEFINITIONS
*********/

collect_references :: [Symredresult sym var tsym tvar] -> [Reference sym] | == sym & == var
collect_references srrs
= [Reference (from_macro&&to_macro) fromsym tosym \\ (fromsym,(from_macro,_,refs)) <- table , (tosym,to_macro) <- refs]
  where table = map (collect_one sym_is_macro sym_arity) srrs
        sym_is_macro = foldmap fst3 False table
        sym_arity = foldmap snd3 noarity table
        noarity = mstub "collect_references" "requesting arity of non-local-function symbol"

collect_one :: (sym->Bool) (sym->Int) (Symredresult sym var tsym tvar) -> (sym,(Bool,Int,[(sym,Bool)])) | == var
collect_one sym_is_macro sym_arity {srr_assigned_symbol=sym,srr_arity=arity,srr_function_def=(_,funcbody)}
= (sym,(macroform funcbody,arity,getoccs funcbody))
  where getoccs funcbody = addoccs sym_is_macro sym_arity funcbody []

addoccs :: (sym->Bool) (sym->Int) (FuncBody sym var) [(sym,Bool)] -> [(sym,Bool)] | == var
addoccs sym_is_macro sym_arity (MatchPattern _ yesbody nobody) rest
= addoccs sym_is_macro sym_arity yesbody (addoccs sym_is_macro sym_arity nobody rest)
addoccs sym_is_macro sym_arity (BuildGraph rgraph) rest
= foldr addnode rest closeds
  where (closeds,_) = graphvars graph [root]
        graph = rgraphgraph rgraph; root = rgraphroot rgraph
        addnode var rest
        = [(sym,cycle_candidate):rest]
          where (_,(sym,args)) = varcontents graph var
                cycle_candidate = sym_is_macro sym && sym_arity sym==length args

macroform (BuildGraph _) = True
macroform (MatchPattern _ _ _) = False

/**********
DETERMINING CYCLES
**********/

getrecursives :: [(sym,[sym])] -> [(sym,Bool)] | == sym
getrecursives refs
= map getrecursive refs
  where getrecursive (sym,directrefs)
        = (sym,isMember sym allrefs)
          where allrefs = getreferenced refs [] directrefs []

getreferenced :: [(sym,[sym])] [sym] [sym] [sym] -> [sym] | == sym
getreferenced refs seen [] referred
= referred
getreferenced refs seen [sym:syms] referred
| isMember sym seen
  = getreferenced refs seen syms referred
= [sym:getreferenced refs [sym:seen] directrefs (getreferenced refs seen syms referred)]
  where directrefs = foldmap id [] refs sym

/*********
DOING THE ACTUAL EXPANSION
*********/

expandone :: [var] (sym->Optional (Rule sym pvar)) (Symredresult sym var tsym tvar) -> Symredresult sym var tsym tvar | == var & == pvar
expandone heap getrule srr=:{srr_assigned_symbol=sym,srr_function_def=(funcargs,funcbody)}
= {srr & srr_function_def = (funcargs,expand_funcbody heap getrule funcbody)}

expand_funcbody :: [var] (sym->Optional (Rule sym pvar)) (FuncBody sym var) -> FuncBody sym var | == var & == pvar
expand_funcbody heap getrule (MatchPattern pattern yesbody nobody)
= MatchPattern pattern (expand_funcbody heap getrule yesbody) (expand_funcbody heap getrule nobody)
expand_funcbody heap getrule (BuildGraph body)
= BuildGraph (mkrgraph newroot newgraph)
  where (_,(newroot,newgraph))
        = foldlr unfoldvar (heap--nodes,(oldroot,oldgraph)) nodes
        nodes
        = varlist oldgraph [oldroot]
        oldgraph
        = rgraphgraph body; oldroot = rgraphroot body
        unfoldvar var heaprootgraph
        | not def
          = heaprootgraph                                       // Do not touch open node-ids
        = foldoptional heaprootgraph unfold (getrule sym)       // Do not touch node-ids with unexpandable symbols; try to expand those with expandable symbols
          where unfold rule
                | eqlen rargs args                              // Check it's not a partial parametrisation
                  = (heap`,(root`,graph`))
                = heaprootgraph                                 // Do not touch partial parametrisations
                  where (heap`,root`,graph`,_) = xunfold var rule (heap,root,graph,mapping)
                        mapping = foldr (uncurry extend) emptypfun (zip2 rargs args)
                        rargs = arguments rule; rroot = ruleroot rule; rgraph = rulegraph rule
                (def,(sym,args)) = varcontents graph root
                (heap,(root,graph)) = heaprootgraph
