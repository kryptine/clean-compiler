definition module classify

import syntax, checksupport, transform

CUnused					:== -1
CPassive   				:== -2
CActive					:== -3
CAccumulating   		:== -4
CVarOfMultimatchCase	:== -5

::	CleanupInfo :== [ExprInfoPtr]

analyseGroups	:: !{# CommonDefs} !{#{#FunType}} !IndexRange !Int !Int !*{! Group} !*{#FunDef} !*VarHeap !*ExpressionHeap 
				-> (!CleanupInfo, !*{!ConsClasses}, !*{!Group}, !*{#FunDef}, !*VarHeap, !*ExpressionHeap)

reanalyseFunction
	:: !Int !FunctionInfoPtr !{# CommonDefs} !{#{#FunType}} !Int !Int !*{#FunDef} !*VarHeap !*FunctionHeap !*{!ConsClasses}
	-> *(!ConsClasses,!*{#FunDef},!*VarHeap,!*FunctionHeap,!*{!ConsClasses})

reanalyseGroups	:: !{# CommonDefs} !{#{#FunType}} !Int !Int ![FunctionInfoPtr]  ![Group] !*{#FunDef} !*VarHeap !*ExpressionHeap !*FunctionHeap !*{!ConsClasses}
				-> (!CleanupInfo, !*{#FunDef}, !*VarHeap, !*ExpressionHeap, !*FunctionHeap, !*{!ConsClasses})
