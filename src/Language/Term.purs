module Language.Term where

import Prelude

import Control.Comonad.Cofree (Cofree, head, tail, (:<))
import Control.Monad.Cont (lift)
import Control.Monad.Error.Class (throwError)
import Control.Monad.Except (ExceptT)
import Control.Monad.State (class MonadState)
import Data.Array (intersperse, replicate)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Eq (class Eq1)
import Data.Eq.Generic (genericEq)
import Data.Foldable (class Foldable, foldMap, foldl, foldr, sequence_)
import Data.Functor.Mu (Mu(..))
import Data.Generic.Rep (class Generic)
import Data.List (List(..), reverse, (:))
import Data.List as List
import Data.List.NonEmpty (NonEmptyList, foldM, zipWith)
import Data.Map as Map
import Data.Maybe (Maybe(..), maybe)
import Data.Ord.Generic (genericCompare)
import Data.Show.Generic (genericShow)
import Data.String.CodeUnits (fromCharArray)
import Data.Traversable (class Traversable, sequence, traverse, traverse_)
import Data.Tuple (Tuple(..), fst, snd)
import Data.Tuple.Nested (type (/\), (/\))
import Effect.Exception (error)
import Language.Kernel.Data (Data(..))
import Language.Lambda.Calculus (class PrettyLambda, class PrettyVar, class Shadow, Lambda, LambdaF(..), PatternF, app, cat, freeIn, freeTyped, prettyVar, replace, replaceFree, shadow, var)
import Language.Lambda.Elimination (class Composition, class Reduction)
import Language.Lambda.Inference (class ArrowObject, class Inference, class IsStar, class IsTypeApp, arrMany, arrow, closeTerm, flat, infer, (:->:))
import Language.Lambda.Module (Module(..), sequenceBindings)
import Language.Lambda.Unification (class Enumerable, class Fresh, class InfiniteTypeError, class NotInScopeError, class Skolemize, class Unify, Skolem, TypingContext, assume, fresh, fromInt, require, rewrite, substitute, unify)
import Language.Lambda.Unification.Error (class ThrowRecursiveModuleError, class ThrowUnificationError, UnificationError(..), recursiveModuleError, unificationError)
import Language.Native (class NativeValue, Native(..))
import Matryoshka.Class.Recursive (project)
import Parsing (ParseError)
import Prettier.Printer (beside, stack, text, (<+>), (</>))
import Pretty.Printer (class Pretty, pretty, prettyPrint)
import Prim (Array, Boolean, Int, Number, Record, String)
import Unsafe.Coerce (unsafeCoerce)

type Term = Lambda Var Var TT

type Pattern = Mu (PatternF Var TT)

type TypedPattern = Cofree (PatternF Var TT) Term

newtype CaseAlternative a
  = CaseAlternative {
      patterns :: NonEmptyList a 
    , guard :: Maybe a 
    , body :: a
    }

derive newtype instance Eq a => Eq (CaseAlternative a)

instance Functor CaseAlternative where
  map f (CaseAlternative a) = CaseAlternative { patterns: map f a.patterns, guard: map f a.guard, body: f a.body }

instance Foldable CaseAlternative where
  foldr f b (CaseAlternative a) = f a.body (foldr f (foldr f b a.patterns) a.guard)
  foldl f b (CaseAlternative a) = f (foldl f (foldl f b a.patterns) a.guard) a.body
  foldMap f (CaseAlternative a) = foldMap f a.patterns <> foldMap f a.guard <> f a.body
 
instance Traversable CaseAlternative where
  traverse f (CaseAlternative a) =
    (\patterns guard body -> CaseAlternative { patterns, guard, body })
      <$> traverse f a.patterns
      <*> traverse f a.guard
      <*> f a.body
  sequence = traverse identity

instance Show (CaseAlternative a) where
  show _ = "TODO: show CaseAlternative"

data TT a =
    Star Int
  | Arrow
  | Let (Module Var a) a 
  | TypeAnnotation a Term
  | TypeLit Term
  | Native (Native Term)
  | Binder String
  | Data (Data Term)
  | Case (NonEmptyList a) (NonEmptyList (CaseAlternative a)) 


-- a Class is a dictionary of types
--  | Class a (Module Var a) a

-- an Instance is a dictionary of terms 
--  | Instance a (Module Var a) a

-- a TypeConstraint brings a type class dictionary into scope
--  | TypeConstraint a a



derive instance Generic (TT a) _

instance NativeValue Mu Var TT where
  native = cat <<< Native
  nativeCat = Native

instance (Pretty a, Show a) => Show (TT a) where
  show (TypeAnnotation a t) = "TypeAnnotation " <> show a <> " " <> show t
  show e = genericShow e

instance IsStar Mu Var Var TT where
  isStar t = case project t of
               Cat (Star _) -> true
               _ -> false

instance IsTypeApp abs Var TT Term where
  isTypeApp t =
    case tail t of
      Cat (TypeLit l) -> Just l
      _ -> Nothing 


instance Functor TT where
  map _ Arrow = Arrow
  map _ (Star i) = Star i
  map f (Let bs a) = Let (f <$> bs) (f a)
  map f (TypeAnnotation a t) = TypeAnnotation (f a) t
  map _ (TypeLit t) = TypeLit t
  map _ (Native n) = Native n 
  map _ (Binder p) = Binder p
  map _ (Data d) = Data d
  map f (Case a e) = Case (map f a) (map f <$> e)

instance Traversable TT where
  traverse _ Arrow = pure Arrow
  traverse _ (Star i) = pure (Star i)
  traverse f (Let bs a) = Let <$> (traverse f bs) <*> f a
  traverse f (TypeAnnotation a t) = flip TypeAnnotation t <$> f a
  traverse _ (TypeLit t) = pure $ TypeLit t
  traverse _ (Native n) = pure $ Native n 
  traverse _ (Binder p) = pure $ Binder p
  traverse _ (Data d) = pure $ Data d
  traverse f (Case o b) = Case <$> traverse f o <*> traverse (traverse f) b
  sequence = traverse identity

instance Skolemize Mu Var TT where
  skolemize (Scoped i s) k = replaceFree (\x -> if x == Ident i then Just (var (Skolemized i s k)) else Nothing) 
  -- TODO error if the Var is not Scoped
  skolemize _ _ = identity

instance Eq a => Eq (TT a) where
  eq = genericEq

instance Eq1 TT where
  eq1 = genericEq

instance Foldable TT where
  foldr _ b (Star _) = b
  foldr _ b Arrow = b
  foldr f b (Let bs bd) = foldr f (f bd b) bs
  foldr f b (TypeAnnotation a _) = f a b
  foldr _ b (TypeLit _) = b
  foldr _ b (Native _) = b
  foldr _ b (Binder _) = b
  foldr _ b (Data _) = b
  foldr f b (Case a e) = foldl (foldr f) (foldr f b a) e
  foldl _ b (Star _) = b
  foldl _ b Arrow = b
  foldl f b (Let bs bd) = f (foldl f b bs) bd
  foldl f b (TypeAnnotation a _) = f b a
  foldl _ b (TypeLit _) = b
  foldl _ b (Native _) = b
  foldl _ b (Binder _) = b
  foldl _ b (Data _) = b
  foldl f b (Case a e) = foldl (foldl f) (foldl f b a) e
  foldMap _ (Star _) = mempty
  foldMap _ Arrow = mempty
  foldMap f (Let bs b) = foldMap f bs <> f b
  foldMap f (TypeAnnotation a _) = f a
  foldMap _ (TypeLit _) = mempty
  foldMap _ (Native _) = mempty
  foldMap _ (Binder _) = mempty
  foldMap _ (Data _) = mempty
  foldMap f (Case a e) = foldMap f a <> foldMap (foldMap f) e

newtype Scope = Scope Int
derive newtype instance Show Scope
derive newtype instance Ord Scope
derive newtype instance Eq Scope


data Var =
    Ident Ident
  | Scoped Ident Scope 
  | Skolemized Ident Scope Skolem


derive instance Generic Var _
instance Show Var where
  show = genericShow
instance Ord Var where
  compare = genericCompare
instance Eq Var where
  eq = genericEq

instance Pretty Var where
  pretty (Ident i) = pretty i
  pretty (Scoped i s) = pretty i <> text (":" <> show s)
  pretty (Skolemized i s k) = pretty i <> text (":" <> show s) <> text (":" <>show k)

instance Shadow Var where
  shadow (Ident i) = Ident i
  shadow (Scoped i _) = Ident i
  shadow (Skolemized i _ _) = Ident i

instance PrettyVar Var where
  prettyVar = pretty

data Ident =
    TypeVar String
  | TermVar String

derive instance Generic Ident _
instance Show Ident where
  show = genericShow
instance Ord Ident where
  compare = genericCompare
instance Eq Ident where
  eq = genericEq

instance Pretty Ident where
  pretty (TypeVar v) = text v
  pretty (TermVar v) = text v

isTypeIdent :: Ident -> Boolean
isTypeIdent (TypeVar _) = true
isTypeIdent _ = false

isTypeVar :: Var -> Boolean
isTypeVar (Ident i) = isTypeIdent i
isTypeVar (Scoped i _) = isTypeIdent i
isTypeVar (Skolemized i _ _) = isTypeIdent i

instance PrettyLambda Void Var TT where
  prettyAbs v _ = absurd v
  prettyApp f a = text "(" <> pretty f <+> pretty a <> text ")"
  prettyCat (Binder p) = text p
  prettyCat (Data d) = pretty d
  prettyCat _  = text "TODO pattern category"

instance PrettyLambda Var Var TT where
  prettyAbs i a | isTypeVar i = text "(forall " <> prettyVar i <+> text "." <+> pretty a <> text ")"
  prettyAbs i a = text "(\\" <> prettyVar i <+> text "->" <+> pretty a <> text ")"
  prettyApp (In (App (In (Cat Arrow)) a)) b = text "(" <> pretty a <+> text "->" <+> pretty b <> text ")"
  prettyApp f a = text "(" <> pretty f <+> pretty a <> text ")"
  prettyCat Arrow = text "->"
  prettyCat (Star i) = text (fromCharArray $ replicate i '*')
  prettyCat (Let (Module bs) a) =
    (text "let" <+> prettyBinds)
                </> (text "in" <+> pretty a)
    where
      -- TODO pull out function args instead of pretty printing lambdas
      prettyBinds = stack (prettyBind <$> Map.toUnfoldable bs)
      prettyBind (v /\ b) = pretty v <+> text "=" <+> pretty b      
  prettyCat (TypeAnnotation v t) = text "(" <> pretty v <+> text "::" <+> pretty t <> text ")"
  prettyCat (TypeLit a) = text "@" <> pretty a
  prettyCat (Native (Purescript { nativePretty })) = text nativePretty
  prettyCat (Binder p) = text p
  prettyCat (Data d) = pretty d
  prettyCat (Case a e) = text "case" <+> foldl beside mempty (pretty <$> a) <+> text "of"
                      </> stack (prettyAlt <$> List.fromFoldable e)
    where prettyAlt (CaseAlternative { patterns, guard, body }) =
            foldl beside mempty (pretty <$> patterns) <+> prettyGuard guard <+> text "=>" <+> pretty body
          prettyGuard = maybe mempty (\g -> text "|" <+> pretty g)



instance ArrowObject (TT a) where
  arrowObject = Arrow 

instance Enumerable Ident where
  fromInt i = TypeVar ("t" <> show i)

instance Enumerable Var where
  fromInt = Ident <<< fromInt


instance Monad m => NotInScopeError Var (ExceptT ParseError (ExceptT (UnificationError Mu Var TT) m)) where 
  notInScopeError = lift <<< throwError <<< NotInScope

instance Monad m => NotInScopeError Var (ExceptT (UnificationError Mu Var TT) m) where 
  notInScopeError = throwError <<< NotInScope

instance Monad m => InfiniteTypeError Var Term (ExceptT ParseError (ExceptT (UnificationError Mu Var TT) m)) where
  infiniteTypeError v t = lift $ throwError $ Err $ "An infinite type was inferred for an expression: " <> prettyPrint t <> " while trying to match type " <> prettyPrint v

instance Monad m => InfiniteTypeError Var Term (ExceptT (UnificationError Mu Var TT) m) where
  infiniteTypeError v t = throwError $ Err $ "An infinite type was inferred for an expression: " <> prettyPrint t <> " while trying to match type " <> prettyPrint v



instance
  ( ThrowUnificationError Term m
  , InfiniteTypeError Var Term m
  , Fresh Var m
  , Skolemize Mu Var TT
  , MonadState (TypingContext Var Mu Var TT) m
  , NotInScopeError Var m
  ) => Unify Var Term m where
  unify v@(Ident i) t =
    case project t of
      Var (Ident j) | i == j -> pure unit
      _ -> substitute v t
  unify v@(Skolemized _ _ i) t =
    case project t of
      Var (Skolemized _ _ j) | i == j -> pure unit
      Var (Skolemized _ _ _) -> unificationError (var v) t
      -- TODO is substitution always safe?                             
      _ -> substitute v t
--      _ -> throwError $ unificationError (var v) t
  unify v@(Scoped _ _) t =
    case project t of
      Var x@(Scoped _ _) | v == x -> pure unit
      -- TODO is substitution always safe?
      _ -> substitute v t


instance
  ( Fresh Var m
  , Skolemize Mu Var TT
  , MonadState (TypingContext Var Mu Var TT) m
  , ThrowUnificationError Term m
  , InfiniteTypeError Var Term m
  , NotInScopeError Var m
  ) => Unify (TT Term) (TT Term) m where
  unify Arrow Arrow = pure unit
  -- TODO cumulativity ~ universe hierarchy
  -- * -> * must be in a higher universe than *
  -- ?? arrow has a dependent type (Star n -> Star m -> Star (max(n,m)+1)
  -- !! constraints must prevent Type in Type
  -- unify (a -> b) * ~> ((a :: *) -> (b :: *))
  unify (Star a) (Star b) | a <= b = pure unit 
  unify (TypeAnnotation a ak) (TypeAnnotation b bk) = unify ak bk  *> unify a b
  unify (TypeAnnotation a _) b = unify a (cat b)
  unify a (TypeAnnotation b _) = unify (cat a) b
  unify a@(Native (Purescript na)) b@(Native (Purescript nb)) = do
    unify na.nativeType nb.nativeType
    when (na.nativePretty /= nb.nativePretty) do
       unificationError (cat a) (cat b)
  unify (Data (DataConstructor a _)) (Data (DataConstructor b _)) | a == b = pure unit
  unify a b = unificationError (cat a) (cat b)

instance
  ( Monad m
  , Unify Term Term m
  , MonadState (TypingContext Var Mu Var TT) m
  , ThrowUnificationError Term m
  , InfiniteTypeError Var Term m
  , NotInScopeError Var m
  ) => Inference Void Var TT Term m where
  inference Arrow = pure $ (arrow (cat (Star 1)) (arrow (cat (Star 1)) (cat (Star 1))) :< Cat Arrow)
  inference (Star i) = pure $ (cat (Star (i+1)) :< Cat (Star i))
  inference (TypeAnnotation v t) = do
    (vt :: Cofree (LambdaF Void Var TT) Term) <- v
    unify (head vt :: Term) t
    vt' <- rewrite (head vt)
    pure (vt' :< tail vt)
  inference (TypeLit t) = pure $ t :< (Cat (TypeLit t))
  inference (Native (Purescript n)) = pure $ n.nativeType :< Cat (Native (Purescript n))
  inference (Binder p) = fresh >>= \t -> let v = Ident $ TermVar p
                                          in do
                                             assume v t
                                             pure (t :< Var v)
  inference (Data (DataConstructor c (Just t))) = pure (t :< Cat (Data (DataConstructor c (Just t)))) 
  inference (Data (DataConstructor c Nothing)) = do
     t <- require (Ident $ TermVar c)
     pure (t :< Cat (Data (DataConstructor c Nothing))) 
--  inference (Data (DataNative (Purescript n))) = pure (n.nativeType :< Cat (Data (DataNative (Purescript n))))
  inference (Data (DataApp a b)) = do
     at <- head <$> infer (cat (Data a) :: Term)
     bt <- head <$> infer (cat (Data b) :: Term)
     pure $ ((app at bt) :< Cat (Data (DataApp a b)))
  inference _ = unsafeCoerce "TODO: this shouldn't be in a pattern" 
 

instance
  ( Monad m
  , Unify Term Term m
  , MonadState (TypingContext Var Mu Var TT) m
  , ThrowUnificationError Term m
  , InfiniteTypeError Var Term m
  , NotInScopeError Var m
  ) => Inference Var Var TT Term m where
  inference Arrow = pure $ (arrow (cat (Star 1)) (arrow (cat (Star 1)) (cat (Star 1))) :< Cat Arrow)
  inference (Star i) = pure $ (cat (Star (i+1)) :< Cat (Star i))
  inference (Let (Module bs) a) = do
     let bx :: List _
         bx = Map.toUnfoldable bs
     flip traverse_ bx $ \(v /\ _) -> do
        t <- fresh
        assume v t
     traverse_ (\(v /\ t) -> do
        t' <- t
        assume v (head t')) bx
     bz <- sequence bs
     t <- a
     pure $ head t :< Cat (Let (Module bz) t)
  inference (TypeAnnotation v t) = do
    (vt :: Cofree (LambdaF Var Var TT) Term) <- v
    unify (head vt :: Term) t
    vt' <- rewrite (head vt)
    pure (vt' :< tail vt)
  inference (TypeLit t) = pure $ t :< (Cat (TypeLit t))
  inference (Native (Purescript n)) = pure $ n.nativeType :< Cat (Native (Purescript n))
  inference (Case args branches) = do
    -- TODO check all branches have the same number of patterns as the args in the case
    -- TODO check all the guards are of type Boolean
    -- TODO check matches are exhaustive
    typedArgs <- sequence args
    let typeBranch (CaseAlternative a) = do
           binds <- sequence a.patterns
           guard <- sequence a.guard
           body <- a.body
           patterns <- traverse (traverse rewrite) binds 
           pure $ CaseAlternative { patterns: patterns, guard, body } 
    typedBranches <- traverse typeBranch branches
    let argTys = head <$> typedArgs 
        getBody (CaseAlternative { body }) = body

    bodies <- map head <$> sequence (getBody <$> branches)
    (t :: Term) <- fresh 
    let unifyAll a b = do
          unify a b
          rewrite a
    argTys' <- traverse rewrite argTys
    caseTy <- foldM unifyAll t bodies
    let unifyBinders (CaseAlternative { patterns }) = do
           sequence_ (zipWith unify argTys' (head <$> patterns :: NonEmptyList Term))
    traverse_ unifyBinders typedBranches 
    pure $ caseTy :< (Cat (Case typedArgs typedBranches))
  inference (Binder p) = fresh >>= \t -> let v = Ident $ TermVar p
                                          in do
                                             assume v t
                                             pure (t :< Var v)
  inference (Data (DataConstructor c (Just t))) = pure (t :< Cat (Data (DataConstructor c (Just t)))) 
  inference (Data (DataConstructor c Nothing)) = do
     t <- require (Ident $ TermVar c)
     pure (t :< Cat (Data (DataConstructor c Nothing))) 
  inference (Data (DataNative n)) = unsafeCoerce "TODO this should be impossible" 
  inference (Data (DataApp a b)) = do
     at <- head <$> infer (cat (Data a) :: Term)
     bt <- head <$> infer (cat (Data b) :: Term)
     pure $ ((app at bt) :< Cat (Data (DataApp a b)))
 

instance
  ( Monad m
  , Unify Term Term m
  , MonadState (TypingContext Var Mu Var TT) m
  , ThrowUnificationError Term m
  , InfiniteTypeError Var Term m
  , NotInScopeError Var m
  ) => Composition Mu Var TT m where
  composition a b ty =
    case tail a /\ tail b of
      Cat (Native (Purescript na)) /\ Cat (TypeLit t) -> do
        case closeTerm $ na.nativeType of
          In (Abs tv tb) -> do
            let tb' = replace (\v -> if shadow v == shadow tv then Just t else Nothing) tb
            pure $ tb' :< Cat (Native (Purescript (na { nativeType = tb' })))
          _ -> pure $ ty :< tail a
      Cat (Native (Purescript na)) /\ Cat (Native (Purescript nb)) -> do
        let nativePretty = "(" <> na.nativePretty <> " " <> nb.nativePretty <> ")"
            nativeType = closeTerm ty
        pure $ ty :< Cat (Native (Purescript { nativeType
                                             , nativePretty
                                             , nativeTerm: na.nativeTerm nb.nativeTerm
                                             }))
      _ -> pure $ ty :< App a b 

instance
  ( Monad m
  , Unify Term Term m
  , MonadState (TypingContext Var Mu Var TT) m
  , ThrowRecursiveModuleError Mu Var TT m
  , NotInScopeError Var m
  , ThrowUnificationError Term m
  , InfiniteTypeError Var Term m
  ) => Reduction Mu Var TT m where
  reduction l t =
    case l of
      Let bi bo -> do
         -- TODO avoid repeated flattening & Map.lookup
         -- & incrementally check free variables
         let Module z = bi
             inline v x =
               case Map.lookup v z of
                 Nothing -> x
                 Just o -> if v `freeIn` (flat x :: Term) then head x :< App ((head o :->: head x) :< Abs v x) o else x
         case sequenceBindings (flat <$> bi) of
           Left err -> recursiveModuleError err
           Right (seq :: List (Var /\ Term)) -> do
              let vars :: List Var
                  vars = fst <$> seq
              pure $ foldl (flip inline) bo vars
      TypeAnnotation f a -> do
         unify (head f) a
         pure $ a :< tail f
      Case args alts -> do 
        (vars :: NonEmptyList Var) <- traverse (const fresh) args
        let argMod :: Module Var TypedTerm
            argMod = Module $ Map.fromFoldable (zipWith Tuple vars args)
            argVars :: NonEmptyList (Var /\ Term)
            argVars = zipWith Tuple vars (head <$> args)
        pure $ t :< Cat (Let argMod (reduceCase argVars t alts))
      c -> pure $ t :< Cat c

type TypedTerm = (Cofree (LambdaF Var Var TT) Term)

reduceCase :: NonEmptyList (Var /\ Term) -> Term -> NonEmptyList (CaseAlternative TypedTerm) -> TypedTerm
reduceCase argVars caseTy branches = appArgs (foldr reduceBranch fallThrough branches) 
  where
    absArgs args b = foldl absArg b args
    absArg b (v /\ t) = (t :->: (head b)) :< Abs v b
    appArgs :: TypedTerm -> TypedTerm
    appArgs b = foldl appArg b argVars
    appArg b (v /\ t) = caseTy :< App b (t :< Var v)
    fallThrough :: TypedTerm
    fallThrough = (arrMany (snd <$> argVars) caseTy) :< Cat (Native $ Purescript {
                            nativeType: caseTy
                          , nativeTerm: unsafeCoerce $ const (error "Pattern match failed.")
                          , nativePretty: "Pattern match failed."
                          })
    reduceBranch :: CaseAlternative TypedTerm -> TypedTerm -> TypedTerm
    reduceBranch (CaseAlternative { patterns, body }) fall =
      let boundVars = foldl append Nil $ freeTyped <$> patterns 
          branch = absArgs boundVars body 
          fallTy = arrMany (snd <$> argVars) caseTy
          branchTy = head branch
          matchTy = branchTy :->: (fallTy :->: fallTy) 

          -- ([a,b,c,...] -> d) -> (\a b c ... -> d)
          liftArgList :: (List (Data Term) -> Match) -> Match
          liftArgList f =
            case List.length $ List.fromFoldable argVars of
              0 -> f Nil
              1 -> Match (unsafeCoerce $ \x -> f (List.singleton x))
              2 -> Match (unsafeCoerce $ \x y -> f (List.fromFoldable [x, y])) 
              3 -> Match (unsafeCoerce $ \x y z -> f (List.fromFoldable [x, y, z])) 
              _ -> unsafeCoerce "needs templating" 

          liftAppList :: Match -> List Match -> Match
          liftAppList (Match f) l = foldl liftApp f l 
            where
              liftApp :: Match -> Match -> Match
              liftApp (Match g) (Match a) = Match (g a) 


          extractPattern :: List (Data Term) -> Maybe (List Match)
          extractPattern = bindPatterns (flat <$> List.fromFoldable patterns)

          matchCase :: (List (Data Term) -> Match) -> (List Match -> Match) -> List (Data Term) -> Match
          matchCase f b = applyMatch f b extractPattern 



          match = matchTy :< Cat (Native (Purescript {
                                 nativeType: matchTy
                                 , nativePretty: "match (" <> Array.fold (intersperse "," (Array.fromFoldable (prettyPrint <$> (flat <$> patterns :: NonEmptyList Term)))) <> ")"
                                , nativeTerm:  --unsafeCoerce $ const $ const $ const (error "Pattern match failed.")
                                    unsafeCoerce $ \branching falling ->
                                      let Match q =
                                            liftArgList $
                                              matchCase (liftAppList (Match (unsafeCoerce falling))
                                                                 <<< map (Match <<< unsafeCoerce)
                                                        )
                                                        (liftAppList (Match (unsafeCoerce branching)))
                                          in q

                                }))
       in fallTy :< App ((fallTy :->: fallTy) :< App match branch) fall 

applyMatch :: forall a b c. (List a -> b) -> (List c -> b) -> (List a -> Maybe (List c)) -> List a -> b
applyMatch fall branch extract args = maybe (fall args) branch (extract args)



newtype Match = Match (forall a. a)

bindPattern :: Term -> Data Term -> Maybe (List Match) 
bindPattern (In (App a b)) (DataApp a' b') = append <$> bindPattern a a' <*> bindPattern b b'
bindPattern t@(In (App _ _)) (DataNative n) = bindPattern t n 
bindPattern (In (Cat (Data c@(DataConstructor _ _)))) c'@(DataConstructor _ _) | c == c' = Just Nil
bindPattern t@(In (Cat (Data (DataConstructor _ _)))) (DataNative n) = bindPattern t n 
bindPattern (In (Var _)) (DataNative n) = Just $ pure $ Match n 
bindPattern _ _ = Nothing

bindPatterns :: List Term -> List (Data Term) -> Maybe (List Match)
bindPatterns pats dats = map join $ sequence $ List.zipWith bindPattern pats dats


