implementation module coreclean

// $Id$

import syntax

:: SuclTypeSymbol
 = SuclUSER TypeSymbIdent
 | SuclFN
 | SuclINT
 | SuclCHAR
 | SuclREAL
 | SuclBOOL
 | SuclDYNAMIC
 | SuclFILE
 | SuclWORLD

:: SuclTypeVariable
 = SuclANONYMOUS Int
 | SuclNAMED TypeVar

sucltypeheap :: [SuclTypeVariable]
sucltypeheap =: map SuclANONYMOUS [0..]

:: SuclSymbol
 = SuclUser Ident

:: SuclSymbolKind
 = SuclFunction
 | SuclConstructor
 | SuclPrimitive

:: SuclVariable
 = SuclAnonymous Int
