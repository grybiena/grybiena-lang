module Language.Term where

import Prelude

import Control.Comonad.Cofree (Cofree, head, tail, (:<))
import Control.Monad.Cont (class MonadTrans, lift)
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
import Data.List (List(..))
import Data.List as List
import Data.List.NonEmpty (NonEmptyList, foldM, singleton, zipWith)
import Data.List.NonEmpty as NonEmptyList
import Data.Map as Map
import Data.Maybe (Maybe(..), maybe)
import Data.Ord.Generic (genericCompare)
import Data.Show.Generic (genericShow)
import Data.String.CodeUnits (fromCharArray)
import Data.Traversable (class Traversable, sequence, traverse, traverse_)
import Data.Tuple (fst)
import Data.Tuple.Nested (type (/\), (/\))
import Effect.Exception (error)
import Language.Kernel.Data (Data(..))
import Language.Lambda.Calculus (class PrettyLambda, class PrettyVar, class Shadow, Lambda, LambdaF(..), app, cat, freeIn, freeTyped, prettyVar, replace, replaceFree, shadow, var)
import Language.Lambda.Elimination (class Composition, class Reduction)
import Language.Lambda.Inference (class ArrowObject, class Inference, class IsStar, class IsTypeApp, arrow, closeTerm, flat, infer, (:->:))
import Language.Lambda.Module (Module(..), sequenceBindings)
import Language.Lambda.Unification (class Enumerable, class Fresh, class InfiniteTypeError, class NotInScopeError, class Skolemize, class Unify, Skolem, TypingContext, assume, fresh, fromInt, infiniteTypeError, notInScopeError, require, rewrite, substitute, unify)
import Language.Lambda.Unification.Error (class ThrowRecursiveModuleError, class ThrowUnificationError, UnificationError(..), recursiveModuleError, unificationError)
import Language.Native (class NativeValue, Native(..))
import Matryoshka.Class.Recursive (project)
import Prettier.Printer (beside, stack, text, (<+>), (</>))
import Pretty.Printer (class Pretty, pretty, prettyPrint)
import Prim (Array, Boolean, Int, Number, Record, String)
import Unsafe.Coerce (unsafeCoerce)

type Term = Lambda Var Var TT


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
  | Pattern String
  | Data (Data Term)
  | Case (NonEmptyList a) (NonEmptyList (CaseAlternative a)) 
  | TTuple (NonEmptyList a)


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
  map _ (Pattern p) = Pattern p
  map _ (Data d) = Data d
  map f (Case a e) = Case (map f a) (map f <$> e)
  map f (TTuple t) = TTuple (map f t)

instance Traversable TT where
  traverse _ Arrow = pure Arrow
  traverse _ (Star i) = pure (Star i)
  traverse f (Let bs a) = Let <$> (traverse f bs) <*> f a
  traverse f (TypeAnnotation a t) = flip TypeAnnotation t <$> f a
  traverse _ (TypeLit t) = pure $ TypeLit t
  traverse _ (Native n) = pure $ Native n 
  traverse _ (Binder p) = pure $ Binder p
  traverse _ (Pattern p) = pure $ Pattern p
  traverse _ (Data d) = pure $ Data d
  traverse f (Case o b) = Case <$> traverse f o <*> traverse (traverse f) b
  traverse f (TTuple t) = TTuple <$> traverse f t
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
  foldr _ b (Pattern _) = b
  foldr _ b (Data _) = b
  foldr f b (Case a e) = foldl (foldr f) (foldr f b a) e
  foldr f b (TTuple t) = foldr f b t
  foldl _ b (Star _) = b
  foldl _ b Arrow = b
  foldl f b (Let bs bd) = f (foldl f b bs) bd
  foldl f b (TypeAnnotation a _) = f b a
  foldl _ b (TypeLit _) = b
  foldl _ b (Native _) = b
  foldl _ b (Binder _) = b
  foldl _ b (Pattern _) = b
  foldl _ b (Data _) = b
  foldl f b (Case a e) = foldl (foldl f) (foldl f b a) e
  foldl f b (TTuple t) = foldl f b t
  foldMap _ (Star _) = mempty
  foldMap _ Arrow = mempty
  foldMap f (Let bs b) = foldMap f bs <> f b
  foldMap f (TypeAnnotation a _) = f a
  foldMap _ (TypeLit _) = mempty
  foldMap _ (Native _) = mempty
  foldMap _ (Binder _) = mempty
  foldMap _ (Pattern _) = mempty
  foldMap _ (Data _) = mempty
  foldMap f (Case a e) = foldMap f a <> foldMap (foldMap f) e
  foldMap f (TTuple t) = foldMap f t

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
  prettyCat (Pattern p) = text p
  prettyCat (Data d) = pretty d
  prettyCat (Case a e) = text "case" <+> foldl beside mempty (pretty <$> a) <+> text "of"
                      </> stack (prettyAlt <$> List.fromFoldable e)
    where prettyAlt (CaseAlternative { patterns, guard, body }) =
            foldl beside mempty (pretty <$> patterns) <+> prettyGuard guard <+> text "=>" <+> pretty body
          prettyGuard = maybe mempty (\g -> text "|" <+> pretty g)
  prettyCat (TTuple t) = text "(" <> Array.fold (intersperse (text ",") (Array.fromFoldable (pretty <$> t)))  <> text ")"



instance ArrowObject (TT a) where
  arrowObject = Arrow 

instance Enumerable Ident where
  fromInt i = TypeVar ("t" <> show i)

instance Enumerable Var where
  fromInt = Ident <<< fromInt



instance Monad m => NotInScopeError Var (ExceptT (UnificationError Mu Var TT) m) where 
  notInScopeError = throwError <<< NotInScope
else
instance
  ( Monad m
  , Monad (t m)
  , MonadTrans t
  , NotInScopeError Var m
  ) => NotInScopeError Var (t m) where 
  notInScopeError = lift <<< notInScopeError 



instance Monad m => InfiniteTypeError Var Term (ExceptT (UnificationError Mu Var TT) m) where
  infiniteTypeError v t = throwError $ Err $ "An infinite type was inferred for an expression: " <> prettyPrint t <> " while trying to match type " <> prettyPrint v
else
instance
  ( Monad m
  , InfiniteTypeError Var Term m 
  , MonadTrans t
  , Monad (t m)
  ) => InfiniteTypeError Var Term (t m) where
  infiniteTypeError v t = lift $ infiniteTypeError v t 



instance
  ( ThrowUnificationError Term m
  , InfiniteTypeError Var Term m
  , Fresh Var m
  , Skolemize Mu Var TT
  , MonadState (TypingContext Var Mu Var TT) m
  , Monad m
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
  , Monad m
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
  unify (TTuple a) (TTuple b) = do
     sequence_ (zipWith unify a b)
  unify a b = unificationError (cat a) (cat b)

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
  inference (TTuple t) = do
     t' <- sequence t
     pure $ ((cat (TTuple (head <$> t')) :< Cat (TTuple t')))
  inference (Data (DataConstructor c (Just t))) = pure (t :< Cat (Data (DataConstructor c (Just t)))) 
  inference (Data (DataConstructor c Nothing)) = do
     t <- require (Ident $ TermVar c)
     pure (t :< Cat (Data (DataConstructor c Nothing))) 
  inference (Pattern c) = do
     t <- require (Ident $ TermVar c)
     pure (t :< Cat (Pattern c)) 
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
--      Cat (Data d) /\ Cat (Data e) -> pure $ ty :< Cat (Data (DataApp d e))
--      Cat (Data d) /\ Cat (Native (Purescript { nativeTerm })) -> do
--        pure $ ty :< Cat (Data (DataApp d (DataNative (unsafeCoerce nativeTerm))))
--      Cat (Native (Purescript na)) /\ Cat (Data d) -> do
--        let nativePretty = "(" <> na.nativePretty <> " " <> prettyPrint (cat (Data d) :: Term) <> ")"
--            nativeType = ty
--        liftEffect $ log $ nativePretty 
--        liftEffect $ log $  prettyPrint (cat (Data d) :: Term)
--        pure $ ty :< Cat (Native (Purescript { nativeType
--                                             , nativePretty
--                                             , nativeTerm: na.nativeTerm d
--                                             }))

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
        let argTy :: Term
            argTy = cat (TTuple (head <$> args))
        pure (t :< App (reduceCase (argTy :->: t) alts) (argTy :< Cat (TTuple args)))
      TTuple z -> do

        let tupCons :: Term -> NonEmptyList Term -> TypedTerm
            tupCons t' lt =
              let nt = t' :->: (cat (TTuple lt)) :->: (cat (TTuple (NonEmptyList.cons t' lt)))
               in nt :< Cat (Native (Purescript { nativeType: nt
                                                , nativeTerm: unsafeCoerce NonEmptyList.cons
                                                , nativePretty: "tupCons"
                                                }))
            tupSing :: Term -> TypedTerm
            tupSing t' = 
              let nt = t' :->: cat (TTuple (singleton t'))
                in nt :< Cat (Native (Purescript { nativeType: nt 
                                                 , nativeTerm: unsafeCoerce NonEmptyList.singleton 
                                                 , nativePretty: "tupSing"
                                                 }))
            build :: NonEmptyList TypedTerm -> TypedTerm
            build w =
              case (NonEmptyList.head w /\ NonEmptyList.fromList (NonEmptyList.tail w)) of
                (u /\ Nothing) ->
                  cat (TTuple (NonEmptyList.singleton (head u))) :< (App (tupSing (head u)) u)
                (u /\ Just so) ->
                     let r = cat (TTuple (NonEmptyList.cons (head u) (head <$> so)))
                         c = (cat (TTuple (head <$> so)) :->: r)
                                :< (App (tupCons (head u) (head <$> so)) u)
                      in r :< App c (build so) 
            out = build z
        pure out 
      c -> pure $ t :< Cat c

type TypedTerm = (Cofree (LambdaF Var Var TT) Term)

freshTermVar = do
  (i :: Int) <- fresh
  pure $ Ident $ TermVar $ "v" <> show i

reduceCase :: Term -> NonEmptyList (CaseAlternative TypedTerm) -> TypedTerm
reduceCase caseTy branches = foldr reduceBranch fallThrough branches
  where
    absArgs args b = foldl absArg b args
    absArg b (v /\ t) = (t :->: (head b)) :< Abs v b
    fallThrough :: TypedTerm
    fallThrough = caseTy :< Cat (Native $ Purescript {
                            nativeType: caseTy
                          , nativeTerm: unsafeCoerce $ const (error "Pattern match failed.")
                          , nativePretty: "Pattern match failed."
                          })
    reduceBranch :: CaseAlternative TypedTerm -> TypedTerm -> TypedTerm
    reduceBranch (CaseAlternative { patterns, body }) fall =
      let boundVars = foldl append Nil $ freeTyped <$> patterns 
          branch = absArgs boundVars body 
          branchTy = head branch
          matchTy = branchTy :->: (caseTy :->: caseTy) 


          liftAppList :: Match -> List Match -> Match
          liftAppList (Match f) l = foldr liftApp f l 
            where
              liftApp :: Match -> Match -> Match
              liftApp (Match a) (Match g) = Match (g a) 


          extractPattern :: NonEmptyList (Data Term) -> Maybe (List Match)
          extractPattern = bindPatterns (flat <$> List.fromFoldable patterns) <<< List.fromFoldable

          matchCase :: (NonEmptyList (Data Term) -> Match)
                    -> (List Match -> Match)
                    -> NonEmptyList (Data Term)
                    -> Match
          matchCase f b = applyMatch f b extractPattern 

          match = matchTy :< Cat (Native (Purescript {
                                 nativeType: matchTy
                                 , nativePretty: "match (" <> Array.fold (intersperse "," (Array.fromFoldable (prettyPrint <$> (flat <$> patterns :: NonEmptyList Term)))) <> ")"
                                , nativeTerm:
                                    unsafeCoerce $ \branching falling arg ->
                                      let Match q =
                                              matchCase falling
                                                        (liftAppList (Match (unsafeCoerce branching)))
                                                        arg
                                          in q

                                }))
       in caseTy :< App ((caseTy :->: caseTy) :< App match branch) fall 

applyMatch :: forall a b c.
              (NonEmptyList a -> b)
           -> (List c -> b)
           -> (NonEmptyList a -> Maybe (List c))
           -> NonEmptyList a -> b
applyMatch fall branch extract args = maybe (fall args) branch (extract args)



newtype Match = Match (forall a. a)

bindPattern :: Term -> Data Term -> Maybe (List Match) 
bindPattern (In (App a b)) (DataApp a' b') = append <$> bindPattern a a' <*> bindPattern b b'
bindPattern t@(In (App _ _)) (DataNative n) = bindPattern t n 
bindPattern (In (Cat (Pattern c))) (DataConstructor c' _) | c == c' = Just Nil
bindPattern t@(In (Cat (Data (DataConstructor _ _)))) (DataNative n) = bindPattern t n 
bindPattern (In (Var _)) (DataNative n) = Just $ pure $ Match n 
bindPattern _ _ = Nothing

bindPatterns :: List Term -> List (Data Term) -> Maybe (List Match)
bindPatterns pats dats = map join $ sequence $ List.zipWith bindPattern pats dats


