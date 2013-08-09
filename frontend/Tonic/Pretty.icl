implementation module Tonic.Pretty

import StdEnv
import Data.Func
import Data.List
import Text.PPrint
import Tonic.AbsSyn
import Tonic.Util
from syntax import :: Expression (..), :: BoundVar {..}, :: App {..}, :: Let, :: Case,
  :: SelectorKind, :: Selection (..), :: FreeVar {..}, :: Global {..}, :: SymbIdent {..}, :: SymbKind, :: Priority,
  :: VarInfoPtr, :: DynamicExpr, :: Ptr, :: VarInfo, :: CodeBinding, :: DefinedSymbol {..}, :: Index,
  :: Bind, :: Position, :: AType, :: Env, :: Ident {..}, :: SymbolPtr, :: SymbolTableEntry, :: Level, :: ExprInfoPtr, :: ExprInfo,
  :: TypeCodeExpression, :: GlobalIndex, :: Conditional, :: BasicValue (..), :: FieldSymbol,
  :: IclModule, :: DclModule, :: FunDef, :: Optional, :: SymbolType, :: LetBind

mkPretty :: InhExpression -> (a -> String) | PP a
mkPretty menv = display o renderCompact o (pp menv)

instance PP [a] | PP a where
  pp inh xs = list (map (pp inh) xs)

instance PP Expression where
  //pp inh expr = exprCata (prettyAlg inh) expr
  pp inh expr = exprCata (debugPPAlg inh) expr

instance PP Ident where
  pp _ i = text i.id_name

instance PP BoundVar where
  pp inh bv = pp inh bv.var_ident

instance PP FreeVar where
  pp inh fv = pp inh fv.fv_ident

instance PP SymbIdent where
  pp inh si = pp inh si.symb_ident

instance PP BasicValue where
  pp _ (BVI str)  = text str
  pp _ (BVInt i)  = int i
  pp _ (BVC str)  = text str
  pp _ (BVB b)    = bool b
  pp _ (BVR str)  = text str
  pp _ (BVS str)  = text str

instance PP DefinedSymbol where
  pp inh ds = pp inh ds.ds_ident

instance PP (Global a) | PP a where
  pp inh glob = pp inh glob.glob_object

instance PP Selection where
  pp inh (RecordSelection gds _)      = pp inh gds
  pp _ (ArraySelection _ _ _)         = text "TODO: ArraySelection"
  pp _ (DictionarySelection _ _ _ _)  = text "TODO: DictionarySelection"

instance PP GExpression where
  pp _ GUndefinedExpression      = text "undef"
  pp _ (GGraphExpression graph)  = text "TODO: render a subgraph (and don't PP one)"
  pp _ (GListExpression ges)     = text "TODO: render a list expression (and don't PP one)"
  //pp _ (GListComprehensionExpression glc)  = text "TODO: render a list comprehension expression (and don't PP one)"
  pp _ (GCleanExpression ce)     = text ce

instance PP GLet where
  pp inh gl = vcat (map (pp inh) gl.glet_binds)

instance PP GLetBind where
  pp inh lb = text lb.glb_dst <+> equals <+> pp inh lb.glb_src

debugPPAlg :: InhExpression -> ExpressionAlg Doc
debugPPAlg inh =
  let
    varC bv = text "<Var>" <+> pp inh bv
    appC app
      # args  = dropAppContexts app inh
      # args  = hcat $ intersperse (text ", ") $ map (pp inh) args
      = text "<App>" <+> pp inh app.app_symb  <+> brackets args
    basicC bv = text "<BasicValue>" <+> pp inh bv
    defaultC = empty
    selectionC _ expr sels = text "<Selection>" <+> pp inh expr <-> char '.' <-> hcat (intersperse (char '.') $ map (pp inh) sels)
    //updateC _ _ _ = text "update"
    //recordUpdateC _ _ _ = text "recordUpdate"
    //tupleSelectC _ _ _ = text "tupleSelect"

  in { mkExprAlg empty
     & var = varC, app = appC, basicExpr = basicC, selection = selectionC }
     //, recordUpdate = recordUpdateC, update = updateC, tupleSelect = tupleSelectC }
