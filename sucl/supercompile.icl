implementation module supercompile

import checksupport
import syntax
import transform
import trans

supercompile
 :: !{# CommonDefs}             // common_defs
    !IndexRange                 // array_instances
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

supercompile _ _ _ _ _ _ _ _ _ _ _ _ = abort "supercompile: not implemented"
