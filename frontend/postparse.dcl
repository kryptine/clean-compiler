definition module postparse

import StdEnv

import syntax, parse, predef

scanModule :: !ParsedModule ![Ident] !Bool !*HashTable !*File !SearchPaths !*PredefinedSymbols (ModTimeFunction *Files) !*Files
	-> (!Bool, !ScannedModule, !IndexRange, ![FunDef], !Optional ScannedModule, ![ScannedModule],!Int,!Int,!*HashTable, !*File, !*PredefinedSymbols, !*Files)
