implementation module coreclean

// $Id$

import strat
import spine
import rule
import graph
import basic
import StdCompare
import syntax
//import StdEnv
import general

:: SuclTypeSymbol
 = SuclUSER (Global Index)
 | SuclFN Int
 | SuclINT
 | SuclCHAR
 | SuclREAL
 | SuclBOOL
 | SuclSTRING
 | SuclDYNAMIC
 | SuclFILE
 | SuclWORLD
 | SuclERROR				// Type error

:: SuclTypeVariable
 = SuclANONYMOUS Int
 | SuclNAMED TypeVar

sucltypeheap :: [SuclTypeVariable]
sucltypeheap =: map SuclANONYMOUS [0..]

:: SuclSymbol
 = SuclUser SymbKind
 | SuclCase ExprInfoPtr
 | SuclApply Int
 | SuclInt Int
 | SuclChar Char
 | SuclReal Real
 | SuclBool Bool
 | SuclString String

:: SuclSymbolKind
 = SuclFunction
 | SuclConstructor
 | SuclPrimitive

:: SuclVariable
 = SuclAnonymous Int
 | SuclNamed VarInfoPtr

suclheap :: [SuclVariable]
suclheap =: map SuclAnonymous [0..]

instance == SuclTypeSymbol
where (==) (SuclUSER tsid1 ) (SuclUSER tsid2 ) = tsid1==tsid2
      (==) (SuclFN   arity1) (SuclFN   arity2) = arity1==arity2
      (==)  SuclINT           SuclINT          = True
      (==)  SuclCHAR          SuclCHAR         = True
      (==)  SuclREAL          SuclREAL         = True
      (==)  SuclBOOL          SuclBOOL         = True
      (==)  SuclSTRING        SuclSTRING       = True
      (==)  SuclDYNAMIC       SuclDYNAMIC      = True
      (==)  SuclFILE          SuclFILE         = True
      (==)  SuclWORLD         SuclWORLD        = True
      (==)  SuclERROR         SuclERROR        = True
      (==)  _                 _                = False

instance toString SuclTypeSymbol
where toString (SuclUSER tsid ) = toString tsid
      toString (SuclFN   arity) = "Arrow/"+++toString arity
      toString  SuclINT         = "Int"
      toString  SuclCHAR        = "Char"
      toString  SuclREAL        = "Real"
      toString  SuclBOOL        = "Bool"
      toString  SuclSTRING      = "String"
      toString  SuclDYNAMIC     = "Dynamic"
      toString  SuclFILE        = "File"
      toString  SuclWORLD       = "World"
      toString  SuclERROR       = "Error"

instance <<< SuclTypeSymbol
where (<<<) file tsym = file <<< toString tsym

instance == SuclTypeVariable
where (==) (SuclANONYMOUS i1) (SuclANONYMOUS i2) = i1 == i2
      (==) (SuclNAMED     p1) (SuclNAMED     p2) = p1 == p2
      (==) _                  _                  = False

instance toString SuclTypeVariable
where toString (SuclANONYMOUS i) = "V_"+++toString i
      toString (SuclNAMED     p) = "N_"+++toString p

instance toString TypeVar
where toString tv = toString tv.tv_info_ptr

instance <<< SuclTypeVariable
where (<<<) file tvar = file <<< toString tvar

instance == SuclSymbol
where (==) (SuclUser  id1  )  (SuclUser  id2  )  = id1   == id2
      (==) (SuclCase  eptr1)  (SuclCase  eptr2)  = eptr1 == eptr2
      (==) (SuclApply int1 )  (SuclApply int2 )  = int1  == int2
      (==) (SuclInt   int1 )  (SuclInt   int2 )  = int1  == int2
      (==) (SuclReal  real1)  (SuclReal  real2)  = real1 == real2
      (==) (SuclBool  bool1)  (SuclBool  bool2)  = bool1 == bool2
      (==) (SuclString str1)  (SuclString str2)  = str1 == str2
      (==) _                  _                  = False

instance toString SuclSymbol
where toString (SuclUser  sk  ) = toString sk
      toString (SuclCase  eptr) = "<anonymous lifted case function for expression "+++toString eptr+++">"
      toString (SuclApply int ) = "Apply/"+++toString int
      toString (SuclInt   int ) = toString int
      toString (SuclReal  real) = toString real
      toString (SuclBool  bool) = toString bool
      toString (SuclString str) = toString str

instance <<< SuclSymbol
where (<<<) file sym = file <<< toString sym

instance toString SymbKind
where toString SK_Unknown = "Unknown"
      toString (SK_Function gi) = "Function "+++toString gi
      toString (SK_LocalMacroFunction i) = "LocalMacroFunction "+++toString i
      toString (SK_OverloadedFunction gi) = "OverloadedFunction "+++toString gi
      toString (SK_Generic gi tk) = "Generic "+++toString gi+++" "+++toString tk
      toString (SK_Constructor gi) = "Constructor "+++toString gi
      toString (SK_Macro gi) = "Macro "+++toString gi
      toString (SK_GeneratedFunction fip i) = "GeneratedFunction "+++toString fip+++" "+++toString i
      toString SK_TypeCode = "TypeCode"

instance <<< SymbKind
where (<<<) file sk = file <<< toString sk

instance toString (Global a) | toString a
where toString {glob_module,glob_object} = toString glob_module+++"."+++toString glob_object

instance toString (Ptr a)
where toString p = "p:"+++toString (ptrToInt p)

instance <<< (Ptr a)
where (<<<) file p = file <<< toString p

instance == SymbKind
where (==) SK_Unknown                       SK_Unknown                      = True
      (==) (SK_Function gi1)                (SK_Function gi2)               = gi1==gi2
      (==) (SK_LocalMacroFunction i1)       (SK_LocalMacroFunction i2)      = i1==i2
      (==) (SK_OverloadedFunction gi1)      (SK_OverloadedFunction gi2)     = gi1==gi2
      (==) (SK_Generic gi1 tk1)             (SK_Generic gi2 tk2)            = gi1==gi2 && tk1==tk2
      (==) (SK_Constructor gi1)             (SK_Constructor gi2)            = gi1==gi2
      (==) (SK_Macro gi1)                   (SK_Macro gi2)                  = gi1==gi2
      (==) (SK_GeneratedFunction fip1 i1)   (SK_GeneratedFunction fip2 i2)  = fip1==fip2 && i1==i2
      (==) SK_TypeCode                      SK_TypeCode                     = True
      (==) _                                _                               = False

instance toString SuclSymbolKind
where toString SuclFunction    = "SuclFunction"
      toString SuclConstructor = "SuclConstructor"
      toString SuclPrimitive   = "SuclPrimitive"

instance <<< SuclSymbolKind
where (<<<) file ssk = file <<< toString ssk

instance == SuclVariable
where (==) (SuclAnonymous i1) (SuclAnonymous i2) = i1 == i2
      (==) (SuclNamed     p1) (SuclNamed     p2) = p1 == p2
      (==) _                  _                  = False

instance toString SuclVariable
where toString (SuclAnonymous i) = "v_"+++toString i
      toString (SuclNamed     p) = "n_"+++toString p

instance <<< SuclVariable
where (<<<) file var = file <<< toString var

// Get the type rule and strictness of a built in core clean symbol

corestricts :: SuclSymbol -> [Bool]
corestricts sym
= case sym
  of (SuclApply argc)
      -> maphd (const True) stricts
     _
      -> stricts
  where stricts = map (const False) (arguments (coretyperule sym))

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
coretyperule (SuclChar _) = consttyperule SuclCHAR
coretyperule (SuclReal _) = consttyperule SuclREAL
coretyperule (SuclBool _) = consttyperule SuclBOOL
coretyperule (SuclString _) = consttyperule SuclSTRING
coretyperule sym = error ("coreclean: coretyperule: untyped user symbol: "+++toString sym)

consttyperule tsym
 = mkrule [] root (updategraph root (tsym,[]) emptygraph)
   where root = SuclANONYMOUS 0

corecomplete :: SuclTypeSymbol -> [SuclSymbol] -> Bool

corecomplete (SuclUSER tsid) = const False  // Must be an abstype...
corecomplete (SuclFN arity) = const False
corecomplete SuclINT = const False
corecomplete SuclCHAR = superset (map (SuclChar o toChar) [0..255]) // 256 alternatives... doubtful is this is useful, but hey...
corecomplete SuclREAL = const False
corecomplete SuclBOOL = superset (map SuclBool [False,True])
corecomplete SuclSTRING = const False
corecomplete SuclDYNAMIC = const False
corecomplete SuclFILE = const False
corecomplete SuclWORLD = const False
corecomplete SuclERROR = const False
