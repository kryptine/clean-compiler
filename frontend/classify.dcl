definition module classify

import syntax, transform

CUnusedLazy				:== -1
CUnusedStrict			:== -2
CPassive   				:== -3
CActive					:== -4
CAccumulating   		:== -5
CVarOfMultimatchCase	:== -6

::	CleanupInfo :== [ExprInfoPtr]

analyseGroups	:: !{# CommonDefs} !{#{#FunType}} !IndexRange !Int !Int !*{! Group} !*{#FunDef} !*VarHeap !*ExpressionHeap 
				-> (!CleanupInfo, !*{!ConsClasses}, !*{!Group}, !*{#FunDef}, !*VarHeap, !*ExpressionHeap)

reanalyseGroups	:: !{# CommonDefs} !{#{#FunType}} !Int !Int ![FunctionInfoPtr]  ![Group] !*{#FunDef} !*VarHeap !*ExpressionHeap !*FunctionHeap !*{!ConsClasses}
				-> (!CleanupInfo, !*{#FunDef}, !*VarHeap, !*ExpressionHeap, !*FunctionHeap, !*{!ConsClasses}, !Bool)

:: *PRState =
	{ prs_group				:: ![Int]
	, prs_cons_args 		:: !*{!ConsClasses}
	, prs_main_dcl_module_n	:: !Int
	, prs_fun_heap			:: !*FunctionHeap
	, prs_fun_defs			:: !*{#FunDef}
	, prs_group_index		:: !Int
	}

class producerRequirements a :: !a !*PRState -> *(!Bool,!*PRState)

instance producerRequirements Expression