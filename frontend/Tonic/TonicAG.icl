/*# LANGUAGE Rank2Types, GADTs #*/
/*# LANGUAGE ScopedTypeVariables #*/


// 1 "./frontend/Tonic/TonicAG.ag"

implementation module TonicAG
// 9 "frontend/Tonic/TonicAG.icl"

// 4 "./frontend/Tonic/TonicAG.ag"

import Control.Monad.Identity
import Control.Applicative
import qualified Control.Monad.Identity as Control.Monad.Identity
from Control.Monad import class Monad (..)
from StdClass import class + (..)
from StdOverloaded import class < (..)
from StdInt import instance + Int, instance < Int
from StdList import ++, foldr, map
import StdMisc
import Data.Void

from Text.PPrint import class Pretty (..), :: Doc
import qualified Text.PPrint as P

import syntax
/*from syntax import :: Expression (..), :: BoundVar, :: App {..}, :: Let, :: Case,*/
  /*:: SelectorKind, :: Selection, :: FreeVar {..}, :: Global, :: SymbIdent, :: Priority,*/
  /*:: VarInfoPtr, :: DynamicExpr, :: Ptr, :: VarInfo, :: CodeBinding, :: DefinedSymbol,*/
  /*:: Bind, :: Position, :: AType, :: Env, :: Ident, :: Level, :: ExprInfoPtr, :: ExprInfo,*/
  /*:: TypeCodeExpression, :: GlobalIndex, :: Conditional, :: BasicValue, :: FieldSymbol*/

// 34 "frontend/Tonic/TonicAG.icl"
// Expression --------------------------------------------------
// wrapper
:: Inh_Expression  = Inh_Expression (ModuleEnv)
moduleEnv_Inh_Expression :: Inh_Expression -> (ModuleEnv)
moduleEnv_Inh_Expression (Inh_Expression x) = x
:: Syn_Expression  = Syn_Expression (Doc) (Doc)
ppDebug_Syn_Expression :: Syn_Expression -> (Doc)
ppDebug_Syn_Expression (Syn_Expression _ x) = x
pp_Syn_Expression :: Syn_Expression -> (Doc)
pp_Syn_Expression (Syn_Expression x _) = x
wrap_Expression :: T_Expression  Inh_Expression  -> (Syn_Expression )
wrap_Expression (T_Expression act) (Inh_Expression alhsImoduleEnv) =
   'Control.Monad.Identity'.runIdentity (
     act >>= \ sem ->
     lift (T_Expression_vIn1 alhsImoduleEnv) >>= \ arg ->
     lift (inv_Expression_s2 sem arg) >>= \ (T_Expression_vOut1 alhsOpp alhsOppDebug) ->
     lift (Syn_Expression alhsOpp alhsOppDebug)
   )

// cata
sem_Expression :: Expression  -> T_Expression 
sem_Expression ( Var bv_ ) = sem_Expression_Var bv_
sem_Expression ( App app_ ) = sem_Expression_App app_
sem_Expression ( At expr_ exprs_ ) = sem_Expression_At ( sem_Expression expr_ ) ( sem_Expressions exprs_ )
sem_Expression ( Let let_ ) = sem_Expression_Let let_
sem_Expression ( Case case__ ) = sem_Expression_Case case__
sem_Expression ( Selection skind_ expr_ sels_ ) = sem_Expression_Selection skind_ ( sem_Expression expr_ ) sels_
sem_Expression ( Update exprl_ sels_ exprr_ ) = sem_Expression_Update ( sem_Expression exprl_ ) sels_ ( sem_Expression exprr_ )
sem_Expression ( RecordUpdate gdsym_ expr_ binds_ ) = sem_Expression_RecordUpdate gdsym_ ( sem_Expression expr_ ) binds_
sem_Expression ( TupleSelect dsym_ n_ expr_ ) = sem_Expression_TupleSelect dsym_ n_ ( sem_Expression expr_ )
sem_Expression ( BasicExpr bv_ ) = sem_Expression_BasicExpr bv_
sem_Expression ( Conditional cond_ ) = sem_Expression_Conditional cond_
sem_Expression ( AnyCodeExpr cbbv_ cbfv_ ss_ ) = sem_Expression_AnyCodeExpr cbbv_ cbfv_ ss_
sem_Expression ( ABCCodeExpr ss_ bl_ ) = sem_Expression_ABCCodeExpr ss_ bl_
sem_Expression ( MatchExpr gdfs_ expr_ ) = sem_Expression_MatchExpr gdfs_ ( sem_Expression expr_ )
sem_Expression ( IsConstructor expr_ gdfs_ arity_ gidx_ ident_ pos_ ) = sem_Expression_IsConstructor ( sem_Expression expr_ ) gdfs_ arity_ gidx_ ident_ pos_
sem_Expression ( FreeVar fv_ ) = sem_Expression_FreeVar fv_
sem_Expression ( DictionariesFunction fvat_ expr_ aty_ ) = sem_Expression_DictionariesFunction fvat_ ( sem_Expression expr_ ) aty_
sem_Expression ( Constant symid_ n_ prio_ ) = sem_Expression_Constant symid_ n_ prio_
sem_Expression ( ClassVariable varinfptr_ ) = sem_Expression_ClassVariable varinfptr_
sem_Expression ( DynamicExpr dynexpr_ ) = sem_Expression_DynamicExpr dynexpr_
sem_Expression ( TypeCodeExpression tycodeexpr_ ) = sem_Expression_TypeCodeExpression tycodeexpr_
sem_Expression ( TypeSignature sigfun_ expr_ ) = sem_Expression_TypeSignature sigfun_ ( sem_Expression expr_ )
sem_Expression ( EE  ) = sem_Expression_EE 
sem_Expression ( NoBind exprinfoptr_ ) = sem_Expression_NoBind exprinfoptr_
sem_Expression ( FailExpr ident_ ) = sem_Expression_FailExpr ident_

// semantic domain
:: T_Expression  = T_Expression (Identity (T_Expression_s2 ))
attach_T_Expression (T_Expression t_Expression) = t_Expression
:: T_Expression_s2  = C_Expression_s2 (T_Expression_v1 )
inv_Expression_s2 (C_Expression_s2 x) = x
:: T_Expression_s3  = C_Expression_s3
:: T_Expression_v1  :== (T_Expression_vIn1 ) -> (T_Expression_vOut1 )
:: T_Expression_vIn1  = T_Expression_vIn1 (ModuleEnv)
:: T_Expression_vOut1  = T_Expression_vOut1 (Doc) (Doc)
sem_Expression_Var :: (BoundVar) -> T_Expression 
sem_Expression_Var arg_bv_ = T_Expression (lift st2) where
   st2 =
        let
        in C_Expression_s2 v1
   /*# LINE 86 "./frontend/Tonic/TonicAG.ag" #*/
   rule0 = \ bv_ ->
                     /*# LINE 86 "./frontend/Tonic/TonicAG.ag" #*/
                     'P'.pretty bv_
                     /*# LINE 100 "frontend/Tonic/TonicAG.icl"#*/
   rule1 = \  (_) ->
     'P'.empty
sem_Expression_App :: (App) -> T_Expression 
sem_Expression_App arg_app_ = T_Expression (lift st2) where
   st2 =
        let
        in C_Expression_s2 v1
   /*# LINE 87 "./frontend/Tonic/TonicAG.ag" #*/
   rule2 = \ ((alhsImoduleEnv)) app_ ->
                     /*# LINE 87 "./frontend/Tonic/TonicAG.ag" #*/
                     let args = dropAppContexts app_ alhsImoduleEnv
                         ppargs xs = 'P'.hcat $ intersperse ('P'.text " ") $ map (pp inh) xs
                     in  (case args of
                            []     -> pp alhsImoduleEnv app_.app_symb
                            [x:xs] -> if (isInfix alhsImoduleEnv app_.app_symb)
                                        (pp alhsImoduleEnv x 'P'. <+> pp alhsImoduleEnv app_.app_symb 'P'. <+> ppargs xs)
                                        (pp alhsImoduleEnv app_.app_symb 'P'. <+> ppargs args))
                     /*# LINE 118 "frontend/Tonic/TonicAG.icl"#*/
   rule3 = \  (_) ->
     'P'.empty
sem_Expression_At :: (T_Expression ) (T_Expressions ) -> T_Expression 
sem_Expression_At arg_expr_ arg_exprs_ = T_Expression (lift st2) where
   st2 =
        let
        in C_Expression_s2 v1
   rule4 = \ ((aexprIpp)) ((aexprsIpp)) ->
     aexprIpp 'P'. <$$> aexprsIpp
   rule5 = \ ((aexprIppDebug)) ((aexprsIppDebug)) ->
     aexprIppDebug 'P'. <$$> aexprsIppDebug
   rule6 = \ ((alhsImoduleEnv)) ->
     alhsImoduleEnv
   rule7 = \ ((alhsImoduleEnv)) ->
     alhsImoduleEnv
sem_Expression_Let :: (Let) -> T_Expression 
sem_Expression_Let _ = T_Expression (lift st2) where
   st2 =
        let
        in C_Expression_s2 v1
   rule8 = \  (_) ->
     'P'.empty
   rule9 = \  (_) ->
     'P'.empty
sem_Expression_Case :: (Case) -> T_Expression 
sem_Expression_Case _ = T_Expression (lift st2) where
   st2 =
        let
        in C_Expression_s2 v1
   rule10 = \  (_) ->
     'P'.empty
   rule11 = \  (_) ->
     'P'.empty
sem_Expression_Selection :: (SelectorKind) (T_Expression ) ([Selection]) -> T_Expression 
sem_Expression_Selection _ arg_expr_ _ = T_Expression (lift st2) where
   st2 =
        let
        in C_Expression_s2 v1
   /*# LINE 94 "./frontend/Tonic/TonicAG.ag" #*/
   rule12 = \ ((aexprIpp)) ((alhsImoduleEnv)) ->
                         /*# LINE 94 "./frontend/Tonic/TonicAG.ag" #*/
                         aexprIpp P   <->   <-> P  char   har '.' P   <->   <-> P  hcat (intersperse (  cat (intersperse (P  char   har '.') $ map (pp alhsImoduleEnv) sels)
                         /*# LINE 161 "frontend/Tonic/TonicAG.icl"#*/
   rule13 = \ ((aexprIppDebug)) ->
     aexprIppDebug
   rule14 = \ ((alhsImoduleEnv)) ->
     alhsImoduleEnv
sem_Expression_Update :: (T_Expression ) ([Selection]) (T_Expression ) -> T_Expression 
sem_Expression_Update arg_exprl_ _ arg_exprr_ = T_Expression (lift st2) where
   st2 =
        let
        in C_Expression_s2 v1
   rule15 = \ ((aexprlIpp)) ((aexprrIpp)) ->
     aexprlIpp 'P'. <$$> aexprrIpp
   rule16 = \ ((aexprlIppDebug)) ((aexprrIppDebug)) ->
     aexprlIppDebug 'P'. <$$> aexprrIppDebug
   rule17 = \ ((alhsImoduleEnv)) ->
     alhsImoduleEnv
   rule18 = \ ((alhsImoduleEnv)) ->
     alhsImoduleEnv
sem_Expression_RecordUpdate :: (Global DefinedSymbol) (T_Expression ) ([Bind Expression (Global FieldSymbol)]) -> T_Expression 
sem_Expression_RecordUpdate _ arg_expr_ _ = T_Expression (lift st2) where
   st2 =
        let
        in C_Expression_s2 v1
   rule19 = \ ((aexprIpp)) ->
     aexprIpp
   rule20 = \ ((aexprIppDebug)) ->
     aexprIppDebug
   rule21 = \ ((alhsImoduleEnv)) ->
     alhsImoduleEnv
sem_Expression_TupleSelect :: (DefinedSymbol) (Int) (T_Expression ) -> T_Expression 
sem_Expression_TupleSelect _ _ arg_expr_ = T_Expression (lift st2) where
   st2 =
        let
        in C_Expression_s2 v1
   rule22 = \ ((aexprIpp)) ->
     aexprIpp
   rule23 = \ ((aexprIppDebug)) ->
     aexprIppDebug
   rule24 = \ ((alhsImoduleEnv)) ->
     alhsImoduleEnv
sem_Expression_BasicExpr :: (BasicValue) -> T_Expression 
sem_Expression_BasicExpr arg_bv_ = T_Expression (lift st2) where
   st2 =
        let
        in C_Expression_s2 v1
   /*# LINE 95 "./frontend/Tonic/TonicAG.ag" #*/
   rule25 = \ ((alhsImoduleEnv)) bv_ ->
                         /*# LINE 95 "./frontend/Tonic/TonicAG.ag" #*/
                         pp alhsImoduleEnv bv_
                         /*# LINE 210 "frontend/Tonic/TonicAG.icl"#*/
   rule26 = \  (_) ->
     'P'.empty
sem_Expression_Conditional :: (Conditional) -> T_Expression 
sem_Expression_Conditional _ = T_Expression (lift st2) where
   st2 =
        let
        in C_Expression_s2 v1
   rule27 = \  (_) ->
     'P'.empty
   rule28 = \  (_) ->
     'P'.empty
sem_Expression_AnyCodeExpr :: (CodeBinding BoundVar) (CodeBinding FreeVar) ([String]) -> T_Expression 
sem_Expression_AnyCodeExpr _ _ _ = T_Expression (lift st2) where
   st2 =
        let
        in C_Expression_s2 v1
   rule29 = \  (_) ->
     'P'.empty
   rule30 = \  (_) ->
     'P'.empty
sem_Expression_ABCCodeExpr :: ([String]) (Bool) -> T_Expression 
sem_Expression_ABCCodeExpr _ _ = T_Expression (lift st2) where
   st2 =
        let
        in C_Expression_s2 v1
   rule31 = \  (_) ->
     'P'.empty
   rule32 = \  (_) ->
     'P'.empty
sem_Expression_MatchExpr :: (Global DefinedSymbol) (T_Expression ) -> T_Expression 
sem_Expression_MatchExpr _ arg_expr_ = T_Expression (lift st2) where
   st2 =
        let
        in C_Expression_s2 v1
   rule33 = \ ((aexprIpp)) ->
     aexprIpp
   rule34 = \ ((aexprIppDebug)) ->
     aexprIppDebug
   rule35 = \ ((alhsImoduleEnv)) ->
     alhsImoduleEnv
sem_Expression_IsConstructor :: (T_Expression ) (Global DefinedSymbol) (Int) (GlobalIndex) (Ident) (Position) -> T_Expression 
sem_Expression_IsConstructor arg_expr_ _ _ _ _ _ = T_Expression (lift st2) where
   st2 =
        let
        in C_Expression_s2 v1
   rule36 = \ ((aexprIpp)) ->
     aexprIpp
   rule37 = \ ((aexprIppDebug)) ->
     aexprIppDebug
   rule38 = \ ((alhsImoduleEnv)) ->
     alhsImoduleEnv
sem_Expression_FreeVar :: (FreeVar) -> T_Expression 
sem_Expression_FreeVar _ = T_Expression (lift st2) where
   st2 =
        let
        in C_Expression_s2 v1
   rule39 = \  (_) ->
     'P'.empty
   rule40 = \  (_) ->
     'P'.empty
sem_Expression_DictionariesFunction :: ([(FreeVar,AType)]) (T_Expression ) (AType) -> T_Expression 
sem_Expression_DictionariesFunction _ arg_expr_ _ = T_Expression (lift st2) where
   st2 =
        let
        in C_Expression_s2 v1
   rule41 = \ ((aexprIpp)) ->
     aexprIpp
   rule42 = \ ((aexprIppDebug)) ->
     aexprIppDebug
   rule43 = \ ((alhsImoduleEnv)) ->
     alhsImoduleEnv
sem_Expression_Constant :: (SymbIdent) (Int) (Priority) -> T_Expression 
sem_Expression_Constant _ _ _ = T_Expression (lift st2) where
   st2 =
        let
        in C_Expression_s2 v1
   rule44 = \  (_) ->
     'P'.empty
   rule45 = \  (_) ->
     'P'.empty
sem_Expression_ClassVariable :: (VarInfoPtr) -> T_Expression 
sem_Expression_ClassVariable _ = T_Expression (lift st2) where
   st2 =
        let
        in C_Expression_s2 v1
   rule46 = \  (_) ->
     'P'.empty
   rule47 = \  (_) ->
     'P'.empty
sem_Expression_DynamicExpr :: (DynamicExpr) -> T_Expression 
sem_Expression_DynamicExpr _ = T_Expression (lift st2) where
   st2 =
        let
        in C_Expression_s2 v1
   rule48 = \  (_) ->
     'P'.empty
   rule49 = \  (_) ->
     'P'.empty
sem_Expression_TypeCodeExpression :: (TypeCodeExpression) -> T_Expression 
sem_Expression_TypeCodeExpression _ = T_Expression (lift st2) where
   st2 =
        let
        in C_Expression_s2 v1
   rule50 = \  (_) ->
     'P'.empty
   rule51 = \  (_) ->
     'P'.empty
sem_Expression_TypeSignature :: (Int Int -> (AType,Int,Int)) (T_Expression ) -> T_Expression 
sem_Expression_TypeSignature _ arg_expr_ = T_Expression (lift st2) where
   st2 =
        let
        in C_Expression_s2 v1
   rule52 = \ ((aexprIpp)) ->
     aexprIpp
   rule53 = \ ((aexprIppDebug)) ->
     aexprIppDebug
   rule54 = \ ((alhsImoduleEnv)) ->
     alhsImoduleEnv
sem_Expression_EE ::   T_Expression 
sem_Expression_EE  = T_Expression (lift st2) where
   st2 =
        let
        in C_Expression_s2 v1
   rule55 = \  (_) ->
     'P'.empty
   rule56 = \  (_) ->
     'P'.empty
sem_Expression_NoBind :: (ExprInfoPtr) -> T_Expression 
sem_Expression_NoBind _ = T_Expression (lift st2) where
   st2 =
        let
        in C_Expression_s2 v1
   rule57 = \  (_) ->
     'P'.empty
   rule58 = \  (_) ->
     'P'.empty
sem_Expression_FailExpr :: (Ident) -> T_Expression 
sem_Expression_FailExpr _ = T_Expression (lift st2) where
   st2 =
        let
        in C_Expression_s2 v1
   rule59 = \  (_) ->
     'P'.empty
   rule60 = \  (_) ->
     'P'.empty

// Expressions -------------------------------------------------
// wrapper
:: Inh_Expressions  = Inh_Expressions (ModuleEnv)
moduleEnv_Inh_Expressions :: Inh_Expressions -> (ModuleEnv)
moduleEnv_Inh_Expressions (Inh_Expressions x) = x
:: Syn_Expressions  = Syn_Expressions (Doc) (Doc)
ppDebug_Syn_Expressions :: Syn_Expressions -> (Doc)
ppDebug_Syn_Expressions (Syn_Expressions _ x) = x
pp_Syn_Expressions :: Syn_Expressions -> (Doc)
pp_Syn_Expressions (Syn_Expressions x _) = x
wrap_Expressions :: T_Expressions  Inh_Expressions  -> (Syn_Expressions )
wrap_Expressions (T_Expressions act) (Inh_Expressions alhsImoduleEnv) =
   'Control.Monad.Identity'.runIdentity (
     act >>= \ sem ->
     lift (T_Expressions_vIn4 alhsImoduleEnv) >>= \ arg ->
     lift (inv_Expressions_s5 sem arg) >>= \ (T_Expressions_vOut4 alhsOpp alhsOppDebug) ->
     lift (Syn_Expressions alhsOpp alhsOppDebug)
   )

// cata
sem_Expressions :: Expressions  -> T_Expressions 
sem_Expressions list = foldr sem_Expressions_Cons sem_Expressions_Nil (map sem_Expression list)

// semantic domain
:: T_Expressions  = T_Expressions (Identity (T_Expressions_s5 ))
attach_T_Expressions (T_Expressions t_Expressions) = t_Expressions
:: T_Expressions_s5  = C_Expressions_s5 (T_Expressions_v4 )
inv_Expressions_s5 (C_Expressions_s5 x) = x
:: T_Expressions_s6  = C_Expressions_s6
:: T_Expressions_v4  :== (T_Expressions_vIn4 ) -> (T_Expressions_vOut4 )
:: T_Expressions_vIn4  = T_Expressions_vIn4 (ModuleEnv)
:: T_Expressions_vOut4  = T_Expressions_vOut4 (Doc) (Doc)
sem_Expressions_Cons :: (T_Expression ) (T_Expressions ) -> T_Expressions 
sem_Expressions_Cons arg_hd_ arg_tl_ = T_Expressions (lift st5) where
   st5 =
        let
        in C_Expressions_s5 v4
   rule61 = \ ((ahdIpp)) ((atlIpp)) ->
     ahdIpp 'P'. <$$> atlIpp
   rule62 = \ ((ahdIppDebug)) ((atlIppDebug)) ->
     ahdIppDebug 'P'. <$$> atlIppDebug
   rule63 = \ ((alhsImoduleEnv)) ->
     alhsImoduleEnv
   rule64 = \ ((alhsImoduleEnv)) ->
     alhsImoduleEnv
sem_Expressions_Nil ::   T_Expressions 
sem_Expressions_Nil  = T_Expressions (lift st5) where
   st5 =
        let
        in C_Expressions_s5 v4
   rule65 = \  (_) ->
     'P'.empty
   rule66 = \  (_) ->
     'P'.empty
