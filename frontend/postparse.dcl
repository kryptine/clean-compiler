definition module postparse

import StdEnv

import syntax, parse, predef

scanModule :: !ParsedModule ![Ident] !Int !*HashTable !*File !SearchPaths !*PredefinedSymbols !*Files
	-> (!Bool, !ScannedModule, !IndexRange, ![FunDef], !Optional ScannedModule, ![ScannedModule],!Int,!Int,!*HashTable, !*File, !*PredefinedSymbols, !*Files)
