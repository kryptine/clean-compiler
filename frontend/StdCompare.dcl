definition module StdCompare

import syntax, compare_constructor

::	CompareValue :== Int
Smaller :== -1
Greater	:== 1
Equal	:== 0

class (=<) infix 4 a :: !a !a -> CompareValue

instance =< Int, Expression, {# Char}, Ident, [a] | =< a, BasicType //, Global a | =< a

instance =< Type

instance == BasicType, TypeVar, TypeSymbIdent, DefinedSymbol, TypeContext , BasicValue,
			FunKind, Global a | == a, Priority, Assoc

export == Int

instance < MemberDef

