implementation module coreclean

// $Id$

import strat
import spine
import rule
import graph
import basic
import StdCompare
import syntax
import syntaxrepr
import Heaprepr

mstub = stub "coreclean"
block func = mstub func "blocked"

:: SuclTypeSymbol
 = SuclUSER (Global Index)
 | SuclTCVAR ConsVariable   // A type constructor variable
 | SuclFN
 | SuclTUPLE Int            // The tuple type of the specified size
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
 | SuclTupleSelect Int Int	// tuple's size and element's index in that order
 | SuclFieldSelect (Global DefinedSymbol) Int
 | SuclArraySelect (Global DefinedSymbol)
 | SuclDictSelect BoundVar // [Selection] // FIXME: from DictionarySelection; what to do with these?
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
where (==) (SuclUSER tsid1) (SuclUSER tsid2) = tsid1==tsid2
      (==) (SuclTCVAR tcv1) (SuclTCVAR tcv2) = tcv1==tcv2
      (==)  SuclFN           SuclFN          = True
      (==) (SuclTUPLE m)    (SuclTUPLE n)    = m==n
      (==)  SuclINT          SuclINT         = True
      (==)  SuclCHAR         SuclCHAR        = True
      (==)  SuclREAL         SuclREAL        = True
      (==)  SuclBOOL         SuclBOOL        = True
      (==)  SuclSTRING       SuclSTRING      = True
      (==)  SuclDYNAMIC      SuclDYNAMIC     = True
      (==)  SuclFILE         SuclFILE        = True
      (==)  SuclWORLD        SuclWORLD       = True
      (==)  SuclERROR        SuclERROR       = True
      (==)  _                _               = False

instance toString SuclTypeSymbol
where toString (SuclUSER tsid ) = toString tsid
      toString (SuclTCVAR tcv1) = toString tcv1
      toString  SuclFN          = "Arrow/2"
      toString (SuclTUPLE n)    = "("+++toString (repeatn (dec n) ',')+++")"
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
      toString (SuclCase  eptr) = "_lift"+++toString eptr
      toString (SuclApply int ) = "Apply/"+++toString int
      toString (SuclInt   int ) = toString int
      toString (SuclReal  real) = toString real
      toString (SuclBool  bool) = toString bool
      toString (SuclString str) = toString str

instance <<< SuclSymbol
where (<<<) file sym = file <<< toString sym

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
where toString (SuclAnonymous i) = "v"+++toString i
      toString (SuclNamed     p) = toString p

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
  where stricts = map (const False) (arguments ((coretyperule--->"coreclean.coretyperule begins from coreclean.corestricts") sym))

coretyperule :: !SuclSymbol -> Rule SuclTypeSymbol SuclTypeVariable
coretyperule (SuclApply argc)
= mkrule [functype:argtypes] restype typegraph
  where (functype,argtypes,typegraph) = mkfuncargtypes sucltypeheap` argc (restype,[],emptygraph)
        [restype:sucltypeheap`] = sucltypeheap
        mkfuncargtypes typeheap 0 rat
        = rat
        mkfuncargtypes [functype,argtype:typeheap] n rat
        = (functype,[argtype:argtypes],updategraph functype (SuclFN,[argtype,restype]) typegraph)
          where (restype,argtypes,typegraph) = mkfuncargtypes typeheap (n-1) rat
coretyperule (SuclTupleSelect tuplesize elemindex)
= mkrule [tupletype] (elemtypes!!elemindex) (updategraph tupletype (SuclTUPLE tuplesize,elemtypes) emptygraph)
  where [tupletype:theap1] = sucltypeheap
        elemtypes = take tuplesize theap1
coretyperule (SuclInt _) = consttyperule SuclINT <--- "coreclean.coretyperule ends (Int)"
coretyperule (SuclChar _) = consttyperule SuclCHAR <--- "coreclean.coretyperule ends (Char)"
coretyperule (SuclReal _) = consttyperule SuclREAL <--- "coreclean.coretyperule ends (Real)"
coretyperule (SuclBool _) = consttyperule SuclBOOL <--- "coreclean.coretyperule ends (Bool)"
coretyperule (SuclString _) = consttyperule SuclSTRING <--- "coreclean.coretyperule ends (String)"
coretyperule sym = error ("coreclean: coretyperule: untyped user symbol: "+++toString sym)

consttyperule tsym
 = mkrule [] root (updategraph root (tsym,[]) emptygraph)
   where root = SuclANONYMOUS 0

corecomplete :: SuclTypeSymbol -> [SuclSymbol] -> Bool

corecomplete (SuclUSER tsid) = const False  // Must be an abstype...
corecomplete (SuclTCVAR tcv) = abort ("Cannot determine completeness of a type constructor variable ("+++toString tcv+++")")
corecomplete SuclFN = const False
corecomplete (SuclTUPLE n) = not o isEmpty  // If there's anything in the list, it's the only tuple constructor
corecomplete SuclINT = const False
corecomplete SuclCHAR = superset (map (SuclChar o toChar) [0..255]) // 256 alternatives... doubtful is this is useful, but hey...
corecomplete SuclREAL = const False
corecomplete SuclBOOL = superset (map SuclBool [False,True])
corecomplete SuclSTRING = const False
corecomplete SuclDYNAMIC = const False
corecomplete SuclFILE = const False
corecomplete SuclWORLD = const False
corecomplete SuclERROR = const False
