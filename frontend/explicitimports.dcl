definition module explicitimports

import syntax, checksupport

possiblyFilterExplImportedDecls :: ![ImportDeclaration] u:[w:(.Index,y:Declarations)] Position u0:{#DclModule} !*CheckState
				-> (!v:[x:(Index,z:Declarations)],!u0:{#DclModule},!.CheckState), [y <= z, w <= x, u <= v]

checkExplicitImportCompleteness :: !Int ![ExplicitImport] !*{#DclModule} !*{#FunDef} !*ExpressionHeap !*CheckState 
				-> (!.{#DclModule},!.{#FunDef},!.ExpressionHeap,!.CheckState)

