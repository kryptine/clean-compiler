implementation module supercompile

// $Id$

import convert
import checksupport
import syntax
import transform
import trans

supercompile
 :: !{# CommonDefs}             // common_defs
    !IndexRange                 // array_instances
    !{#DclModule}               // dcl_mods
    !Int                        // main_dcl_module_n
    !*{! Group}                 // components
    !*{#FunDef}                 // fun_defs
    !*VarHeap                   // var_heap
    !*ExpressionHeap            // expression_heap
    !{#{#FunType}}              // imported_funs
    !*{#{#CheckedTypeDef}}      // dcl_types
    !ImportedConstructors       // used_conses_in_dynamics
    !*TypeDefInfos              // type_def_infos
    !*TypeHeaps                 // type_heaps

 -> (   !*{!Group}              // components
    ,   !*{#FunDef}             // fun_defs
    ,   !*{#{#CheckedTypeDef}}  // dcl_types
    ,   !ImportedConstructors   // used_conses
    ,   !*VarHeap               // var_heap
    ,   !*TypeHeaps             // type_heaps
    ,   !*ExpressionHeap        // expression_heap
    )

supercompile common_defs array_instances dcl_mods main_dcl_module_n components fun_defs var_heap expression_heap imported_funs dcl_types used_conses_in_dynamics type_def_infos type_heaps
= (components,fun_defs,dcl_types,used_conses,var_heap,type_heaps,expression_heap)
  where used_conses = abort "supercompile: not implemented"
		// Determine defined functions
        _ = cts_function fun_defs
		// Determine exported functions
        _ = cts_exports fun_defs dcl_mods main_dcl_module_n
        // Convert sucl-generated function body back to core clean
        (expression_heap`,var_heap`,func_body) = stc_funcdef dcl_mods expression_heap var_heap undef
