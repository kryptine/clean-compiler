implementation module supercompile

// $Id$

import convert
import newtest
import cli
import coreclean
import basic
import checksupport
import syntax
import transform
import trans

supercompile ::
    !{#DclModule}               // dcl_mods
    !Int                        // main_dcl_module_n
    !*{#FunDef}                 // fun_defs
    !*VarHeap                   // var_heap
    !*ExpressionHeap            // expression_heap
    !*PredefinedSymbols         // Predefined symbol table
    !*File                      // Log file
 -> (   !*{#FunDef}             // fun_defs
    ,   !*VarHeap               // var_heap
    ,   !*ExpressionHeap        // expression_heap
    ,   IndexRange              // Range of newly generated functions (already existing functions are overwritten)
    ,   !.PredefinedSymbols     // Consulted predefined symbol table
    ,   !.File                  // Written log file
    )

supercompile dcl_mods main_dcl_module_n fun_defs0 var_heap expression_heap predefs0 logfile0
  # logfile = stderr
    // Determine defined functions
  # (sucl_typerules,sucl_stricts,sucl_bodies,sucl_kinds,fun_defs1) = cts_function main_dcl_module_n fun_defs0
    // Determine exported functions
  # (predefs1,sucl_exports) = cts_exports dcl_mods predefs0 main_dcl_module_n
    // Get constructor lists of algebraic types
  # sucl_constrs = cts_getconstrs dcl_mods
    // Build abstract CLI module
  # sucl_module = mkcli sucl_typerules sucl_stricts sucl_exports sucl_constrs sucl_bodies
    // Generate fresh function symbols
  # (n_fun_defs,fun_defs3) = usize fun_defs1
  # fresh_symbols = [SuclUser (SK_Function (mkglobal main_dcl_module_n i)) \\ i<-[n_fun_defs..]]
    // Do the job!
  # logfile = logfile <<< "Start fullsymred." <<< nl
  # symredresults = fullsymred fresh_symbols sucl_module
  # logfile = sfoldl (<<<) (logfile<<<"All symredresults." <<< nl) symredresults
  # n_symredresults = length symredresults
  # logfile = logfile <<< "Number of generated functions: " <<< n_symredresults <<< nl
    // Create and fill new fundef array
  # (pds,predefs2) = predefs1![PD_StringType]
  # (expression_heap`,var_heap`,fundefs4) = stc_funcdefs pds dcl_mods main_dcl_module_n n_fun_defs expression_heap var_heap symredresults fun_defs3
    // Determine which were the newly generated functions
  # (newlimit,fundefs5) = usize fundefs4
  # generated_range = {ir_from=n_fun_defs,ir_to=newlimit}
  # logfile = logfile <<< "New functions from " <<< n_fun_defs <<< " to " <<< newlimit <<< " (not included)" <<< nl
  # logfile = logfile <<< "Remaining " <<< (n_symredresults-(newlimit-n_fun_defs)) <<< " should be exported" <<< nl
= logfile $ (fundefs5,var_heap`,expression_heap`,generated_range,predefs2,logfile0)

mkglobal gmod gob = {glob_module = gmod, glob_object = gob}

showbody (sym,rules) = "("+++toString sym+++","+++listToString rules+++")"
