definition module postparse

import StdEnv

import syntax, parse, predef

scanModule :: !ParsedModule !*HashTable !*File !SearchPaths !*PredefinedSymbols !*Files
	-> (!Bool, !ScannedModule, !IndexRange, ![FunDef], !ScannedModule, !ScannedModule, ![ScannedModule], !*HashTable, !*File, !*PredefinedSymbols, !*Files)
