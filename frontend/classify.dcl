definition module classify

import syntax, checksupport, transform

cPassive   				:== -1
cActive					:== -2
cAccumulating   		:== -3
cVarOfMultimatchCase	:== -4

::	CleanupInfo :== [ExprInfoPtr]

analyseGroups	:: !{# CommonDefs} !{#{#FunType}} !IndexRange !Int !Int !*{! Group} !*{#FunDef} !*VarHeap !*ExpressionHeap 
				-> (!CleanupInfo, !*{! ConsClasses}, !*{! Group}, !*{#FunDef}, !*VarHeap, !*ExpressionHeap)

