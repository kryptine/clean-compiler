implementation module coreclean

// $Id$

import syntax

:: SuclTypeSymbol
 = SuclINT

:: SuclTypeVariable
 = SuclANONYMOUS Int

:: SuclSymbol
 = SuclUser Ident

:: SuclSymbolKind
 = SuclFunction
 | SuclConstructor
 | SuclPrimitive

:: SuclVariable
 = SuclAnonymous Int
