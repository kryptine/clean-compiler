definition module parse

import syntax, hashtable, scanner, predef

::	*ParseErrorAdmin = 
	{	pea_file	:: !*File
	,	pea_ok		:: !Bool
	}

cWantIclFile :== True	
cWantDclFile :== False	

wantModule :: !Bool !Ident !Position !Bool !*HashTable !*File !SearchPaths !*PredefinedSymbols (ModTimeFunction *Files) !*Files
	-> (!Bool, !ParsedModule, !*HashTable, !*File, !*PredefinedSymbols, !*Files)
