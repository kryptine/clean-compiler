implementation module coreclean

// $Id$

import strat
import spine
import rule
import graph
import syntax

:: SuclTypeSymbol
 = SuclUSER TypeSymbIdent
 | SuclFN Int
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
 | SuclReal Real
 | SuclBool Bool

:: SuclSymbolKind
 = SuclFunction
 | SuclConstructor
 | SuclPrimitive

:: SuclVariable
 = SuclAnonymous Int
 | SuclNamed VarInfoPtr

suclheap :: [SuclVariable]
suclheap =: map SuclAnonymous [0..]

instance == SuclSymbol
where (==) (SuclUser  sptr1)  (SuclUser  sptr2)  = sptr1 == sptr2
      (==) (SuclCase  eptr1)  (SuclCase  eptr2)  = eptr1 == eptr2
      (==) (SuclApply int1 )  (SuclApply int2 )  = int1  == int2
      (==) (SuclInt   int1 )  (SuclInt   int2 )  = int1  == int2
      (==) (SuclReal  real1)  (SuclReal  real2)  = real1 == real2
      (==) (SuclBool  bool1)  (SuclBool  bool2)  = bool1 == bool2
      (==) _                  _                  = False

instance == SuclVariable
where (==) (SuclAnonymous i1) (SuclAnonymous i2) = i1 == i2
      (==) (SuclNamed     p1) (SuclNamed     p2) = p1 == p2
      (==) _                  _                  = False

// Get the type rule and strictness of a built in core clean symbol
coretypeinfo :: SuclSymbol -> (Rule SuclTypeSymbol SuclTypeVariable,[Bool])
coretypeinfo sym
 = (trule,corestricts sym)
   where corestricts (SuclApply argc) = [True,False]
         corestricts sym = map (const False) (arguments trule)
         trule = coretyperule sym

coretyperule :: SuclSymbol -> Rule SuclTypeSymbol SuclTypeVariable
coretyperule (SuclApply argc)
 = mkrule [infunctype,argtype] outfunctype` (updategraph infunctype (SuclFN argc,[argtype:argtypes]++[restype]) outfuncgraph)
   where [infunctype,outfunctype,argtype,restype:sucltypeheap`] = sucltypeheap
         argtypes = take argc sucltypeheap`
         (outfunctype`,outfuncgraph)
          = if (argc==0)
               (restype,emptygraph)
               (outfunctype,updategraph outfunctype (SuclFN (argc-1),argtypes++[restype]) emptygraph)
coretyperule (SuclInt _) = consttyperule SuclINT
coretyperule (SuclReal _) = consttyperule SuclREAL
coretyperule (SuclBool _) = consttyperule SuclBOOL
coretyperule (SuclUser _) = abort "coreclean: coretyperule: untyped user symbol"
coretyperule (SuclCase _) = abort "coreclean: coretyperule: untyped case symbol"

consttyperule tsym
 = mkrule [] root (updategraph root (tsym,[]) emptygraph)
   where root = SuclANONYMOUS 0
