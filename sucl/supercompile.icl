implementation module supercompile

// $Id$

import convert
import newtest
import cli
import coreclean
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
 -> (   !*{#FunDef}             // fun_defs
    ,   !*VarHeap               // var_heap
    ,   !*ExpressionHeap        // expression_heap
    )

supercompile dcl_mods main_dcl_module_n fun_defs0 var_heap expression_heap
= (fundefs4,var_heap`,expression_heap`)
  where // Determine defined functions
        (sucl_typerules,sucl_stricts,sucl_bodies,sucl_kinds,fun_defs1) = cts_function main_dcl_module_n fun_defs0
		// Determine exported functions
        sucl_exports = cts_exports dcl_mods main_dcl_module_n
		// Get constructor lists of algebraic types
		sucl_constrs = cts_getconstrs dcl_mods
        // Build abstract CLI module
        sucl_module = mkcli sucl_typerules sucl_stricts sucl_exports sucl_constrs sucl_bodies
        // Generate fresh function symbols
        (n_fun_defs,fun_defs3) = usize_u fun_defs1
        fresh_symbols = [SuclUser (SK_Function (mkglobal main_dcl_module_n i)) \\ i<-[n_fun_defs..]]
        // Do the job!
        symredresults = fullsymred fresh_symbols sucl_module
        // Create and fill new fundef array
        (expression_heap`,var_heap`,fundefs4) = stc_funcdefs dcl_mods main_dcl_module_n n_fun_defs expression_heap var_heap symredresults fun_defs3

mkglobal gmod gob = {glob_module = gmod, glob_object = gob}
