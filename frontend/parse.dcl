definition module parse

import syntax, hashtable, scanner, predef

::	*ParseErrorAdmin = 
	{	pea_file	:: !*File
	,	pea_ok		:: !Bool
	}

cWantIclFile :== True	
cWantDclFile :== False	

wantModule :: !Bool !Ident !*HashTable !*File !SearchPaths !*PredefinedSymbols !*Files
	-> (!Bool, !ParsedModule, !*HashTable, !*File, !*PredefinedSymbols, !*Files)
