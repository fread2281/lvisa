{-# LANGUAGE PatternSynonyms, TemplateHaskell, OverloadedLists, TypeApplications, AllowAmbiguousTypes, ScopedTypeVariables, PolyKinds, MagicHash, UndecidableInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, PartialTypeSignatures #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

module Core where

-- import Data.HashMap.Lazy as M
import Lib.Fin
-- import GHC.TypeLits (CmpNat)
import Text.PrettyPrint.ANSI.Leijen hiding ((<>),(<$>),Pretty(..))
-- import GHC.TypeLits.Witnesses
import Data.Singletons.Prelude.Num
import Data.Singletons.TypeLits
import Data.Singletons.Prelude.Bool
import Data.Singletons.Prelude.Eq
import Data.Singletons.Decide
import Solver.Class
import Solver.Ref
import Data.IORef
import Lib.Misc
import Text.Parsix (Span)
import System.IO.Unsafe


data MetaType n = IsType | HasType (Type n)
  deriving (Generic)
newtype ScopeVar n = ScopeVar Int
  deriving (Show)

data ScopeInfo n where
  SimpleScope :: HashMap Text (Type n, Term n) -> ScopeInfo n
  -- ConstraintScope :: 
  SolverScope :: KnownNat n => Sing k -> ScopeVar n -> ScopeInfo (n + k)
  

-- TODO: better blame
-- TODO: mb rename this so constraints only refer to internal constraints (typeclasses etc)
data AConstraint where
  -- `m = y : b`, using subtyping to convert `x : a` to `y : b`
  Subtype :: Blame -> Env n -> Type n -> Type n -> Term n -> MetaVar n -> AConstraint
  -- `m : e -> whatever` (iirc it's `e -> a -> b` for now, might want `e -> a = b` in the future)
  Unify :: Blame -> Env n -> Type n -> Type n -> Term n -> MetaVar n -> AConstraint
  Unify_ :: Blame -> Env n -> Core n -> Core n -> AConstraint
  -- `m = x : b`, solving the tele var and then the meta once we know the head of t
  -- expects `m : b`, sets `m = x` once we know if `x : a` needs an implicit lambda.
  -- reduces to a subtype constraint, `a >= b`
  -- order is `SubtypeTele _ _ _ a x b m`, expects `m : b`
  -- SubtypeTele :: Blame -> Env n -> TeleTyVar n -> Type (n + 1) -> Term (n + 1) -> Type n -> MetaVar n -> AConstraint
  -- `m : t ~ x in s`
  -- meta order is `ty tm`
  LookupName :: Blame -> Env n -> [ScopeInfo n] -> Text -> MetaVar n -> MetaVar n -> AConstraint
  DefineScope :: Env n -> ScopeVar n -> [ScopeInfo n] -> AConstraint
  -- DefineName :: Blame -> Env n -> ScopeVar n -> Text -> Type n -> Term n -> AConstraint

data ElabState = ElabState {
  _idSupply :: Int,
  -- TODO: make sure this is a good design or works at all or w/e
  -- TODO: currently just using normal metas...
  -- _levelMap :: HashMap LevelVar (),
  -- Int = exists n. ScopeVar n
  _scopeMap :: HashMap Int (Some (Compose [] ScopeInfo)),
  _constraints :: [AConstraint],
  -- TODO: replace this with a streaming thing so we can send feedback
  -- before we're done
  _warnings :: [Warning]
} deriving (Generic)
  

-- | Warnings & "errors"
-- 
-- for now, we crash on haskell errors, later we'll have error recovery if typechecking
-- functions cause haskell errors (TODO) so use haskell errors if something goes terribly wrong,
-- and otherwise avoid errors (try to always produce something runnable!)
data Warning = OtherWarning Doc


-- TODO: s/String/Doc/ probably
data Blame = Blame String Span
  deriving (Show)

data MetaVar (n :: Nat) = MetaVar {
  _metaEnv :: Env n,
  _metaType :: MetaType n,
  _metaVal :: MVar (MVarT (StateT ElabState (VaultT IO))) (Term n),
  --  ^ hack to avoid having to parameterize data structures by the monad stack
  -- (will probably use module parameters a la agda for this once we have them)
  -- eventually will be like `MVarT (BacktrackingT (VaultT IO))` or similar
  _metaId :: IORef (Maybe Int),
  -- ^ used for printing, only assigned if it's actually printed
  -- TODO: do something nicer for this
  -- maybe have a monad for printing terms that names & collects metas it references
  -- so we can also print their types etc
  _metaSource :: Blame
} deriving (Generic)

instance Eq (MetaVar n) where
  (==) = (==) `on` _metaVal

metaCounter :: IORef Int
metaCounter = unsafePerformIO $ newIORef 0
{-# NOINLINE metaCounter #-}

-- TODO: this is EXTREMELY hacky,
-- should replace it with a better solution!
displayedMetas :: IORef [Some MetaVar]
displayedMetas = unsafePerformIO $ newIORef []
{-# NOINLINE displayedMetas #-}

instance Show (MetaVar n) where
  show m = (++) "_" $ show $ unsafePerformIO $ do
    v <- readIORef $ _metaId m
    case v of
      Nothing -> do
        v' <- atomicModifyIORef metaCounter (\i -> (i+1, i))
        modifyIORef displayedMetas (Some m:)
        atomicModifyIORef (_metaId m) $ \case
          Nothing -> (Just v', v')
          Just v'' -> (Just v'', v'')
      Just v' -> pure v'
instance Pretty (MetaVar n) where
  prettyPrec _ = magenta . text . show



-- TODO: figure out what information we need to be able to store for automated refactoring
-- just use another data type, run normal elaboration & also grab type info etc alongside
-- might want api for like running elaboration with extra output data
-- so only need stuff for type error reporting in Core
-- TODO: or try to do resugaring into macros for display???
-- maybe at some point, but reversing arbitrary macros needs lots of machinery

-- TODO: maybe this should cache its level?
newtype Type n = TypeC (Core n) deriving (Generic, Pretty, Show)
newtype Term n = TermC (Core n) deriving (Generic, Pretty, Show)

-- TODO: currently we're using the normal tele vars for levels, should we?
{-
-- a element of a level telescope
newtype LevelTeleElemVar = LevelTeleElemVar Int

data LevelSeq = LevelSeq (Seq (Either LevelTeleElemVar Level))

-- a level telescope (list of levels)
newtype LevelTeleTyVar = LevelTeleTyVar Int
-}

-- TODO: type Env n = Telescope 0 n 

data Env n where
  EmptyEnv :: Env 0
  -- needed to deal w/ scoping for levels correctly
  -- (internally, we're a la agda ish.
  -- the restriction on levels is that they don't have a lambda & Level doesn't have a type)
  -- we want level-polymorphic let, so telescopes need to be able to mix
  -- levels & types
  -- TODO: with this level system, could have lsup
  -- TODO: is there some uniformity condition that we need to be able to always evaluate levels out? might lsup break it?
  -- 
  -- TODO: is exposing Env ok if we use it like this?
  -- TODO: want to make it possible to store level env in elab monad
  -- (require reentry (there's gotta be a better name for this) when level abstractions might be inserted)

  -- TODO: would be nice to also be able to implement api with type:type or a fixed number of levels or no polymorphism
  -- SnocLevelTele :: LevelTele -> Env n -> Env n
  SnocEnvTy :: Env n -> Text -> Type n -> Env (n + 1)
  -- SnocEnvConstraint :: Env n -> Core n -> Env (n + 1)

-- so, let's figure out how to do tidy:
-- we want to keep track of which variable names come from the source
-- & for variable that come from implicit lam,
-- we should use the expected type & what the variable is used for
-- as a hint for what name to generate
-- e.g. (id,id,id) : forall {a1, a2, a3}. (a1 -> a1, a2 -> a2, a3 -> a3)
-- if `id :: forall {a}. a -> a`
-- i think?


-- Telescope n m is a telescope starting in n env with m entries
-- TODO: implicits
-- remember that Env n ~= Telescope 0 n
-- (morally, TODO: make it literally true)
data Telescope :: Nat -> Nat -> * where
  TeleExplicitTy :: Text -> Core n -> Telescope (n + 1) m -> Telescope n (1 + m)
  TeleImplicitTy :: Text -> Core n -> Telescope (n + 1) m -> Telescope n (1 + m)
  TeleConstraint :: Core n -> Telescope (n + 1) m -> Telescope n (1 + m)
  -- TODO: figure out if we want this (i.e. tele var lam/pi)
  -- (w/o it substing for tele vars is simpler)
  -- TeleVar :: TeleTyVar -> Telescope (n + 1) m -> Telescope n (m + 1)
  TeleEmpty :: Telescope n 0

teleNames :: Telescope n m -> [Maybe Text]
teleNames (TeleExplicitTy n _ t) = Just n:teleNames t
-- teleNames (TeleVar _ t) = Nothing:teleNames t
teleNames TeleEmpty = []

appendTele :: forall n m o. Telescope n m -> Telescope (n + m) o -> Telescope n (m + o)
appendTele TeleEmpty t = t
appendTele (TeleExplicitTy n ty (r :: Telescope (n + 1) p)) t = gcastWith (assoc @1 @p @o) $ gcastWith (assoc @n @1 @p) $ TeleExplicitTy n ty (appendTele r t)
appendTele (TeleImplicitTy n ty (r :: Telescope (n + 1) p)) t = gcastWith (assoc @1 @p @o) $ gcastWith (assoc @n @1 @p) $ TeleImplicitTy n ty (appendTele r t)
appendTele (TeleConstraint ty (r :: Telescope (n + 1) p)) t = gcastWith (assoc @1 @p @o) $ gcastWith (assoc @n @1 @p) $ TeleConstraint ty (appendTele r t)

appEnvTele :: forall n m. Env n -> Telescope n m -> Env (n + m)
appEnvTele e (TeleExplicitTy n ty r) = appEnvTele (SnocEnvTy e n $ coerce ty) r
appEnvTele e TeleEmpty = e

teleRecoverNat :: Telescope n m -> Sing m
teleRecoverNat TeleEmpty = SNat @0
teleRecoverNat (TeleExplicitTy _ _ (r :: Telescope _ m)) = teleRecoverNat r %+ SNat @1


-- instance Pretty (Telescope n m) where
  -- prettyPrec _ = 


deriving instance Show (Env n)


instance Pretty (Env n) where
  prettyPrec p e = parensif (p > 0) $ go mempty mempty e where
    go2 :: HashMap Text NameOcc -> Seq String -> Env m -> Doc
    go2 _ _ EmptyEnv = ""
    go2 o m e = go o m e <> ", "
  
    go :: HashMap Text NameOcc -> Seq String -> Env m -> Doc
    go o m EmptyEnv = ""
    go o m (SnocEnvTy e "" (TypeC t)) = go2 o ([""] <> m) e <> prettyCore mempty 0 mempty t
    go o m (SnocEnvTy e n (TypeC t)) = go2 o ([unpack n] <> m) e <> text (unpack n) <> " : " <> prettyCore mempty 0 mempty t

envNames :: Env n -> Seq String
envNames = fromList . fmap unpack . f where
  f :: Env n -> [Text]
  f EmptyEnv = []
  f (SnocEnvTy e n _) = n:f e


envRecoverNat :: forall n r. Env n -> Sing n
envRecoverNat EmptyEnv = SNat @0
envRecoverNat (SnocEnvTy (e :: Env m) _ _) = envRecoverNat e %+ SNat @1

-- TODO: metadata:
-- * termination info?
-- are we elabing to fix or not?
-- can we reuse occurs check here?
-- * variables?
-- * more?


-- newtype LevelVar = LevelVar Int
--   deriving (Eq, Ord, Hashable)

-- newtype TelePath = TelePath [Int]

-- TODO: need level env to do well-typed levels
-- probably dual envs or such when typed :|
-- for now, we're going with "lsup" but no equalities on it, and try to reduce it to lmax
-- simple, easy :)
-- so `Level n` is `Term e Level`
newtype Level n = LevelTerm (Core n)
  deriving (Show)

-- levelMax :: Level n -> Text -> Level (n + 1) -> Level n
-- levelMax i j = App LSup []


-- rule is can't abstract over universe-polymorphic functions
-- but can let-define universe polymorphic functions
-- simplest is just to have the env have type schemes
-- nat is number of telescope variables

-- likely going to need to do (mostly?) untyped syntax :(
-- due to telescope variables...
-- TODO: let's just keep it as-is, and insert a few unsafeCoerces :)

data Constant =
  -- : (i : Level) -> Type i
  TypeP |
  -- Level type, but not : anything
  Level |
  -- : (i : Level) -> (a : Type i) -> (a -> Level) -> Level
  LSup |
  -- : Level
  LLit Int |
  -- forall X, : X
  Assume
  deriving (Show, Eq, Generic)

instance Pretty Constant where
  prettyPrec p = dullgreen . \case
    TypeP -> "Type"
    Level -> "Level"
    LSup -> "lsup"
    LLit 0 -> "lzero"
    LLit n -> "level_" <> text (show n)


-- order is: name, unique, type
-- hacky for now, TODO: rethink this once we have modules
data DataCon n = DataCon Text Int (Core n)

data CaseAlt n where
  -- m = number of arguments
  -- TODO: store a tele here?
  CaseAlt :: KnownNat m => DataCon n -> Sing m -> Core (n + m) -> CaseAlt n

-- TODO: let, optimize
-- TODO: shadow trees for names?
data Core :: Nat -> * where
  Lam :: KnownNat m => Telescope n m -> Core (n + m) -> Core n
  Pi :: KnownNat m => Telescope n m -> Core (n + m) -> Core n
  -- NOTE: Bound & Meta are used for tele vars in the arg list of App
  -- (for lambda/pi-bound tele vars and metas standing for elements of the sigma type)
  -- TODO: probably change that when we optimize app
  App' :: Core n -> Seq (Core n) -> Core n
  Bound :: Fin n -> Core n
  -- Invariant: m = length of env of meta
  Meta :: MetaVar m -> Subst m n -> Core n
  -- int is a globally unique variable
  -- could use e.g. `IORef ()` instead (w/ pointer equality)
  -- always fails occurs check, etc
  -- used for lamM
  Free :: Int -> Core n
  -- TODO:
  -- Meta :: MetaVar m -> Subst m n -> Core n
  -- SomeLevel :: Level n -> Core n
  -- TODO: make sure the user can't use this, doesn't get it returned, etc
  -- TODO: or we could remove level & go fully coq-style & have special handling fohr metas
  -- TODO: gotta make sure meta solving doesn't allow `\(x : Level) -> f x` where it shouldn't be
  -- lsup : (i : Level) -> (A : Set j) -> (A -> Level) -> Level
  ConstC :: Constant -> Core n
  -- lsup : (i : Level) (A : Set i) (j : A -> Level) -> Level
  -- https://lists.chalmers.se/pipermail/agda/2013/005502.html
  -- LSup :: Core n
  -- -- | dlub (Type i) n x (Type j) = Type (lsup i x (\n -> j))
  -- DLub :: Core n -> Text -> Core n -> Core (n + 1) -> Core n
  -- SubstMeta :: MetaVar -> Core 0 -> Core n -> Core n
  -- Subst :: S m (Core n) -> Core m -> Core n
  Constructor :: DataCon n -> Core n
  -- ty, expr, body of P : ty -> Type
  -- each alt should be of type P (C args)
  -- & Case is of type P x
  Case :: Type n -> Core n -> Type (n + 1) -> [CaseAlt n] -> Core n
  -- a reference to a top-level definition
  -- w/ its value inline
  -- might be part of a recursive definiton, so be careful when expanding this!
  -- TODO: expand this for let rec & modules etc
  -- or maybe do away with this & store this in tables?
  -- idk
  -- this forces us to be one-pass or do knot-tying carefully
  -- could put a meta here always?
  Ref :: Text -> Core n -> Core n

newtype Subst (m :: Nat) (n :: Nat) = Subst (Fin m -> Core n)
  deriving (Generic)

instance Pretty (Subst m n) where
  prettyPrec _ _ = "_"

instance Category Subst where
  id = Subst Bound
  f . Subst g = Subst (subst f . g)

substSkip :: forall o n m. Sing o -> Subst n m -> Subst (n + o) (m + o)
substSkip SNat (Subst f) = Subst (splitFin @_ @o (shiftN @m @o . f) (Bound . weakenFin))

subst1 :: Core n -> Core (n + 1) -> Core n
subst1 x = subst $ Subst (either Bound (const x) . finSplit' @_ @1)

subst :: forall n m. Subst n m -> Core n -> Core m
subst (Subst a) = runIdentity . traverseSubst (\_ -> Identity . a) g where
  g :: Sing o -> MetaVar k -> Subst k (n + o) -> Identity (Core (m + o))
  g o mv ms = Identity $ Meta mv (substSkip o (Subst a) . ms)

substExtend :: Subst n (n + 1)
substExtend = Subst (extendCore . Bound)

substAt1 :: Core r -> Subst n r -> Subst (n + 1) r
substAt1 a (Subst b) = undefined

-- bool is if var is rigid or not
traverseSubst :: forall f m n. Applicative f =>
  (Bool -> Fin n -> f (Core m)) ->
  (forall o k. Sing o -> MetaVar k -> Subst k (n + o) -> f (Core (m + o))) ->
  Core n -> f (Core m)
-- traverseSubst f g = undefined
traverseSubst f g = go True
    (\(SNat :: Sing o) b v ->
      either
      (\v' -> shiftN @m @o @0 <$> f b v')
      (pure . Bound . weakenFin)
      $ finSplit' @n @o v
      )
    g 
  where
  go :: forall f n m. Applicative f => Bool ->
    (forall o. Sing o -> Bool -> Fin (n + o) -> f (Core (m + o))) ->  
    (forall o k. Sing o -> MetaVar k -> Subst k (n + o) -> f (Core (m + o))) ->
    Core n -> f (Core m)
  go rv f g (Lam (t :: Telescope n m2) b) = Lam <$> go_tele rv f g t <*> go rv (\o -> f (SNat @m2 %+ o)) (\o -> g (SNat @m2 %+ o)) b
  go rv f g (Pi (t :: Telescope n m2) b) = Pi <$> go_tele rv f g t <*> go rv (\o -> f (SNat @m2 %+ o)) (\o -> g (SNat @m2 %+ o)) b

  go rv f g (App' x@(Constructor _) xs) = App <$> go rv f g x <*> traverse (go rv f g) xs
  go rv f g (App' x@(ConstC _) xs) = App <$> go rv f g x <*> traverse (go rv f g) xs
  go rv f g (App' x xs) = App <$> go rv f g x <*> traverse (go False f g) xs
  go rv f _ (Bound v) = f (SNat @0) rv v
  go rv _ g (Meta m s) = g (SNat @0) m s
  go _ _ _ (ConstC c) = pure $ ConstC c
  go rv f g (Constructor (DataCon n i ty)) = Constructor . DataCon n i <$> go rv f g ty
  -- TODO: is this right?
  -- need to be careful here!
  go rv f g (Ref n x) = Ref n <$> go rv f g x
  go rv f g (Case ty v p alts) = Case <$> (coerce <$> go rv f g (coerce ty)) <*> go rv f g v <*> (coerce <$> go rv (\o -> f (SNat @1 %+ o)) (\o -> g (SNat @1 %+ o)) (coerce p)) <*> traverse (go_alt rv f g) alts
  go _ _ _ x = error $ show x

  go_alt :: forall f n m. Applicative f => Bool ->
    (forall o. Sing o -> Bool -> Fin (n + o) -> f (Core (m + o))) ->  
    (forall o k. Sing o -> MetaVar k -> Subst k (n + o) -> f (Core (m + o))) ->
    CaseAlt n -> f (CaseAlt m)
  go_alt rv f g (CaseAlt (DataCon n i con) m x) = CaseAlt <$> (DataCon n i <$> go rv f g con) <*> pure m <*> go rv (\o -> f (m %+ o)) (\o -> g (m %+ o)) x


  go_tele :: forall f n m l. Applicative f => Bool ->
    (forall o. Sing o -> Bool -> Fin (n + o) -> f (Core (m + o))) ->  
    (forall o k. Sing o -> MetaVar k -> Subst k (n + o) -> f (Core (m + o))) ->
    Telescope n l -> f (Telescope m l)
  go_tele rv f g TeleEmpty = pure TeleEmpty
  go_tele rv f g (TeleExplicitTy n ty r) = TeleExplicitTy n <$> go rv f g ty <*> go_tele rv (\o -> f (SNat @1 %+ o)) (\o -> g (SNat @1 %+ o)) r
  go_tele rv f g (TeleImplicitTy n ty r) = TeleImplicitTy n <$> go rv f g ty <*> go_tele rv (\o -> f (SNat @1 %+ o)) (\o -> g (SNat @1 %+ o)) r

-- -- TODO
-- traverseCore :: forall f m n. Applicative f =>
--   (BoundV n -> f (Core m)) -> Core n -> f (Core m)
-- traverseCore f = traverseSubst (\_ -> f) g where
--   g :: forall o k. Sing o -> MetaVar k -> Subst k (n + o) -> f (Core (m + o))
--   g s mv ms = _

shiftN :: forall i j k. (KnownNat k, KnownNat j) => Core (i + k) -> Core (i + j + k)
shiftN = case SNat @j %~ SNat @0 of
  Proved Refl -> id
  _ -> subst $ Subst (Bound . shiftNV @i @j @k)


-- question is how 2 do well-typed modules...
-- obvious thing is like current module is a well-typed like partial dag
-- need to figure out termination checking
-- graph, nodes are definitions, edges are deps labelled with size info or w/e
-- & known modules are maybe just ordered?

extendCore :: Core n -> Core (n + 1)
extendCore = subst $ Subst (Bound . finSucc)

bound = Bound

-- add a env element on the left end
weakenCore :: Core n -> Core (1 + n)
weakenCore = unsafeCoerce



closedCore :: Core 0 -> Core n
closedCore = unsafeCoerce


parensif :: Bool -> Doc -> Doc
parensif True a = text "(" <> a <> text ")"
parensif False a = a

-- TODO: | Reserved | ...
data NameOcc = Used



prettyTele :: HashMap Text NameOcc -> Seq String -> Telescope n m -> Doc
-- prettyTele o m (TeleVar v t) = "*" <> pretty v <> " " <> prettyTele o (pure "" <> m) t
prettyTele o m (TeleExplicitTy "" v t) = prettyCore o 4 m v <> " " <> prettyTele o (pure "" <> m) t
prettyTele o m (TeleExplicitTy n v t) = "(" <> text (unpack n) <> " : " <> prettyCore (o & at n ?~ Used) 0 m v <> ") " <> prettyTele o (pure (unpack n) <> m) t
prettyTele o m (TeleImplicitTy n v t) = "{" <> text (unpack n) <> " : " <> prettyCore (o & at n ?~ Used) 0 m v <> "} " <> prettyTele o (pure (unpack n) <> m) t
prettyTele o m TeleEmpty = ""

-- TODO: this Seq should be SeqWithLength n
prettyCore :: HashMap Text NameOcc -> Int -> Seq String -> Core n -> Doc
prettyCore o p m (Lam t b) = parensif (p > 0) $ text "\\" <> prettyTele o m t <> "→ " <> prettyCore o 0 (fromList (reverse $ fmap (unpack . fromMaybe "") $ teleNames t) <> m) b
prettyCore o p m (Pi t b) = parensif (p > 0) $ prettyTele o m t <> "→ " <> prettyCore o 0 (fromList (reverse $ fmap (unpack . fromMaybe "") $ teleNames t) <> m) b
prettyCore o p m (App' a bs) = parensif (p > 3) $ "@" <> prettyCore o 3 m a <> foldMap (\b -> text " " <> prettyCore o 4 m b) bs
-- prettyCore o p m (Subst v x) = prettyCore o 4 mempty x <> "[" <> pretty v <> "]"
prettyCore o p _ (Meta m s) = pretty m <> "[" <> pretty s <> "]"
-- TODO: use showsPrec
prettyCore o p _ (ConstC x) = prettyPrec p x
prettyCore o p m (Constructor (DataCon n _ x)) = dullgreen $ text (unpack n) -- "(" <> text (unpack n) <> " : " <> prettyCore o p m x <> ")"
-- prettyCore o p m (SomeLevel (LevelTerm t)) = prettyCore o p m t
-- prettyCore o p m (DLub a n x b) = parensif (p > 3) $ text "dlub " <> prettyCore o 4 m a <> text " " <> text (unpack n) <> text " " <> prettyCore o 4 m x <> text " " <> prettyCore o 4 (pure (unpack n) <> m) b
-- prettyCore o _ _ (Bound v) = text $ show v
prettyCore o p m (Case _ x _ xs) = "[case|" <> prettyCore o p m x <> " of " <> foldMap g xs <> "]"
  where g (CaseAlt (DataCon c _ _) _ r) = text (unpack c) <> " -> " <> prettyCore o p mempty r <> "; "
  -- where go xs = 
prettyCore o p m (Ref n _) = text (unpack n)
prettyCore o _ m (Bound f) = case m ^? ix (fromIntegral $ finVal f) of
  Just n | n /= "" -> text n
  _ -> text (show f)

instance Pretty (Core n) where
  prettyPrec p = prettyCore mempty 4 mempty
instance Show (Core n) where
  show = show . prettyPrec 0

-- prettyCore o p m (Let n i v b) = parensif (p > 0) $ text "let " <> text (unpack n) <> text " = " <> prettyCore o 0 m v <> text " in " <>prettyCore o (M.insert i n m) b


-- prettyV p m (Bound i) = case M.lookup i m of
--   Just v -> text $ unpack v
--   Nothing -> parensif (p > 0) (text $ "Bound " ++ show i)
-- prettyV _ _ (Free a) = text $ unpack a



pattern App :: Core t -> Seq (Core t) -> Core t
pattern App a bs <- App' a bs where
  App (App a bs) cs = App a (bs <> cs)
  App a Empty = a
  App a bs = App' a bs

-- Type : Term e level -> Type e
-- want `Type : (l : Term e lvl) -> Term e (el (Type $ lsuc l))`
-- or `Type_code : (l : Term e lvl) -> Term e (Type $ lsuc l)`
-- question: does the first work?
pattern Type :: Core t -> Core t
pattern Type lvl <- App' (ConstC TypeP) [lvl] where
  Type lvl = App (ConstC TypeP) [lvl]



is_implicit_pi :: Core n -> Maybe Bool
is_implicit_pi = go where
  go :: Core n -> Maybe Bool
  go (App (ConstC c) _) = Just False
  go (Pi (TeleImplicitTy _ _ _) _) = Just True
  go (Pi (TeleExplicitTy _ _ _) _) = Just False
  go (Bound _) = Just False
  -- TODO: this is wrong sometimes (when s = SubstOne etc)
  -- go (Subst s x) = go x
  go (Constructor _) = Just False
  go _ = Nothing
-- is_implicit_pi _ = Just False


makeWrapped ''Type
makeWrapped ''Term
makeLenses ''MetaVar
