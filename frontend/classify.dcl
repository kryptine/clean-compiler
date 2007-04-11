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
