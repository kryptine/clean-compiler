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
 = SuclUser SymbolPtr
 | SuclCase ExprInfoPtr
 | SuclApply Int
 | SuclInt Int
 | SuclChar Char
 | SuclBool Bool

:: SuclSymbolKind
 = SuclFunction
 | SuclConstructor
 | SuclPrimitive

:: SuclVariable
 = SuclAnonymous Int
 | SuclNamed VarInfoPtr

instance == SuclVariable
where (==) (SuclAnonymous i1) (SuclAnonymous i2) = i1 == i2
      (==) (SuclNamed     p1) (SuclNamed     p2) = p1 == p2
      (==) _                  _                  = False
