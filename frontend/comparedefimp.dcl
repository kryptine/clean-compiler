definition module comparedefimp

import syntax, checksupport

// compare definition and implementation module

compareDefImp :: !{#Int} !{!FunctionBody} !Int !{#CheckedTypeDef} !DclModule !*IclModule !*Heaps !*ErrorAdmin 
				-> (!.IclModule,!.Heaps,!.ErrorAdmin)

symbolTypesCorrespond :: !SymbolType !SymbolType !*TypeHeaps -> (!ComparisionErrorCode, !.TypeHeaps)

:: ComparisionErrorCode :== Int
// arg n not ok: n
CEC_ResultNotOK :== 0
CEC_Ok :== -1
CEC_ArgNrNotOk :== -2
CEC_ContextNotOK :== -3
CEC_AttrEnvNotOK :== -4
