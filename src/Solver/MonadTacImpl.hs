{-# LANGUAGE ExistentialQuantification, GeneralizedNewtypeDeriving, TemplateHaskell, OverloadedLists, ScopedTypeVariables, TypeApplications, AllowAmbiguousTypes, DeriveDataTypeable, UndecidableInstances #-}
-- {-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
module Solver.MonadTacImpl where

import Solver.MonadTac
import Core
import Lib.Fin
import Lib.Misc
-- import qualified GHC.TypeNats
import qualified Control.Concurrent.MVar as MV
import Data.IORef
-- import GHC.TypeLits.Witnesses
-- import Solver.MonadTacTypes
import Solver.Unify
-- import Data.Singletons.Prelude
import Data.Singletons.Prelude
import Data.Singletons.TypeLits
-- import Data.IntSet (IntSet)
-- import Control.Monad.Fail
-- import Data.Data (Data)
-- import Data.Data.Lens
-- import qualified Text.PrettyPrint.ANSI.Leijen as P
import Data.Bitraversable
import Solver.Class
import Solver.Ref

-- for now, we're going to store constraint context in env (just do linear traversal of env when solving)
-- remember: whereever it's stored needs to be accessible by subtype & modifibile by subtypeTele / tele vars
-- so env is the obvious thing
-- conceptually, it could be split from env i think, but simpler to not

-- TODO: need to be able to suspend macro execution for efficiency & readTerm
-- TODO: refactor to avoid big StateT


instance Pretty Warning where
  prettyPrec _ (OtherWarning d) = d


instance Pretty (MetaType n) where
  prettyPrec _ IsType = "type"
  prettyPrec _ (HasType ty) = pretty ty

-- instance Pretty MetaInfo where
--   prettyPrec _ (MetaInfo e ty v b blx) = "(" <> pretty e <> " ⊢ " <> x <> maybe "" ((" = " <>) . prettyCore mempty 0 ns . coerce) v <> " (" <> pretty b <> ")" <> ")" <> (if null blx then "" else " blocked")
--     where x = case ty of IsType -> "type"; HasType ty -> prettyCore mempty 0 ns $ coerce ty
--           ns = envNames e
--   -- prettyPrec _ = text . show


-- idea for metas: do (MetaValues -> a) inside
-- so we can verify

-- or maybe a like Fix (PartialMetaValues ->)?
newtype ElabMonad a = ElabMonad (MVarT (StateT ElabState (VaultT IO)) a)
  deriving (Functor, Applicative, Monad, MonadIO, MonadState ElabState, MonadFail, MVish)

makeLenses ''ElabState

instance Pretty ElabState




zonk_state :: ElabMonad ()
zonk_state = do
  s <- get
  -- TODO: clean tele vars
  -- this should really just be s & template clean_metas
  -- but no Data.Data instances for GADTs :(
  put =<< (pure s -- >>= (metaMap.each) f
                  >>= (scopeMap.each) k)
  where
    -- f (MetaInfo e ty v s blx) = MetaInfo <$> g e <*> h ty <*> traverse i v <*> pure s <*> pure blx
    g :: Env n -> ElabMonad (Env n)
    g EmptyEnv = pure EmptyEnv
    g (SnocEnvTy r n ty) = SnocEnvTy <$> g r <*> pure n <*> j ty
    -- g (SnocEnvVar r v) = SnocEnvVar <$> g r <*> pure v
    h :: MetaType n -> ElabMonad (MetaType n)
    h IsType = pure IsType
    h (HasType ty) = HasType <$> j ty
    i :: Term n -> ElabMonad (Term n)
    i = fmap coerce . zonk_term . coerce
    j :: Type n -> ElabMonad (Type n)
    j = fmap coerce . zonk_term . coerce
    k :: Some (Compose [] ScopeInfo) -> ElabMonad (Some (Compose [] ScopeInfo))
    k (Some x) = Some <$> (_Wrapped.each) l x
    l :: ScopeInfo n -> ElabMonad (ScopeInfo n)
    l (SimpleScope m) = SimpleScope <$> traverse (bitraverse j i) m


-- instance PP.Pretty ElabState where
--   pretty (ElabState _ ms ss tvs cs) = _




initialState :: Int -> ElabState
initialState s = ElabState s mempty mempty mempty

prelude :: MonadScope m => m (ScopeSet m 0)
prelude = newScope EmptyEnv $ [
  ("Type", TypeC $ Type (ConstC $ LLit 1), TermC $ Type $ ConstC $ LLit 0)
  ]


runElabMonad :: ElabMonad a -> IO (a, ElabState)
runElabMonad (ElabMonad m) = do
  var <- MV.newEmptyMVar
  s <- m & flip runMVarT (liftIO . MV.putMVar var) & flip runStateT (initialState 0) & runVaultT
  v <- MV.readMVar var
  pure (v, snd $ fst s)

-- appEnv :: Env n -> Core 0 -> Core n
-- appEnv e t = envRecoverNat e $ go e t
--   where
--     go :: forall n. KnownNat n => Env n -> Core 0 -> Core n
--     go EmptyEnv r = r
--     go (SnocEnvVar (v :: Env m) _) r =
--       withDict (f (Dict :: Dict (KnownNat n))) $
--       App (extendCore (go v r)) [Bound finZ]
--     go (SnocEnvTy (v :: Env m) _) r = 
--       withDict (f (Dict :: Dict (KnownNat n))) $
--       App (extendCore (go v r)) [Bound finZ]
--     f :: forall (n :: Nat) (m :: Nat). (n ~ (m + 1)) => Dict (KnownNat n) -> Dict (KnownNat m)
--     f Dict = withNatOp (%-) (Proxy :: Proxy n) (Proxy :: Proxy 1) $
--       unsafeCoerce (Dict :: Dict (KnownNat (n - 1)))


-- newtype Subst n m = Subst (Core n -> Core m)

-- TODO: is this actually what assign needs?
-- matchEnv a b, checks b is a subtype of a, (that b is a ++ p)
-- and returns substitutions if we needed to expand tele vars while doing it
-- (cps'd because sigma in haskell is annoying)
-- matchEnv :: Env n -> Env m -> (forall o p. Env o -> Telescope o p -> Subst n o -> Subst m (o + p) -> r) -> ElabMonad r
-- matchEnv a b f = _
-- -- matchEnv (SnocEnvTy v ty) (SnocEnvTy v2 ty2) f = matchEnv v v2 $ \a b s t -> f (SnocEnvTy a _) _ _ _

-- TODO: problem for tactics:
-- shouldn't ask them to be able to deal w/ envs chaning out from under them?
-- what do then?
-- expanding definitions/metas calls matchEnv or such
-- could invert substitutions?

-- FIXME: question: does eager tele var solving actually do anything more general than blocking?
-- maxsmt. figure out if there's some way to make ~blocking work well w/ maxsmt

-- feasibility of not having implicit abstraction:
-- need at least `\y -> b` = `\{x} y -> b`
-- is there a simpler way to do only impliinstance Pretty MetaInfo where
--   prettyPrec _ (MetaInfo e ty v b blx) = "(" <> pretty e <> " ⊢ " <> x <> maybe "" ((" = " <>) . prettyCore mempty 0 ns . coerce) v <> " (" <> pretty b <> ")" <> ")" <> (if null blx then "" else " blocked")
--     where x = case ty of IsType -> "type"; HasType ty -> prettyCore mempty 0 ns $ coerce ty
--           ns = envNames e
--   -- prettyPrec _ = text . showcits before an explicit? not really i think

newMeta' :: Blame -> Env n -> MetaType n -> ElabMonad (MetaVar n)
newMeta' b e ty = do
  r <- liftIO $ newIORef Nothing
  v <- newMVar
  pure $ MetaVar {
    _metaEnv = e,
    _metaType = ty,
    _metaVal = v,
    _metaId = r,
    _metaSource = b
  }
  -- v <- idSupply %%= (\x -> (x, x+1))
  -- metaMap.at v .= Just (MetaInfo e ty Nothing b [])
  -- pure $ coerce v

-- TODO: add to the blames for tracking or such?
instance MonadMeta ElabMonad where
  newMeta b e ty = do
    v <- newMeta' b e $ HasType ty
    pure (v,TermC $ Meta v id)
  newTypeMeta b e = do
    v <- newMeta' b e IsType
    pure (v,TypeC $ Meta v id)
  -- assertIsType b e (ty, val)  = do
  --   TermC lvl <- newMeta b e (TypeC $ ConstC Level)
  --   TermC c <- coe b e ty (TypeC $ Type lvl) val
  --   pure (LevelTerm lvl, TypeC c)
instance MonadConstraints ElabMonad where
  -- instantiating tele vars & implicits + unification
  -- also can insert implicit lambdas on the rhs (but the rhs can't refer to the implicitly bound var)
  -- subtype b x y v expects v : x, returns w : y
  subtype b e x y v = try_subtype b e x y v >>= \case
    Just v' -> pure v'
    Nothing -> do
      m <- newMeta' b e (HasType y)
      constraints <>= [Subtype b e x y v m]
      pure $ TermC $ Meta m id
  -- subtypeTele b e (Principal (x,v)) y = subtype b e x y v
  -- subtypeTele b e (Nonprincipal t (x,v)) y = try_subtypetele b e t x v y >>= \case
  --   Just v' -> pure v'
  --   Nothing -> do
  --     m <- newMeta' b e $ HasType y
  --     constraints <>= [SubtypeTele b e t x v y m]
  --     pure $ TermC $ Meta m id
  -- TODO: fast path
  unify_ b e x y = constraints <>= [Unify_ b e x y]
  -- TODO: mb return an equality instead of doing a coercion here?
  -- like that's the type unify should have for macros
  unify b e x y v = try_unify b e x y >>= \s -> case s of Just True -> pure v; _ -> coerce g e x y v
    where
      g e x y v = do
        m <- newMeta' b e $ HasType (TypeC y)
        constraints <>= [Unify b e (TypeC x) (TypeC y) v m]
        pure $ Meta m id
  -- newTeleVar e = do
  --   id <- idSupply %%= (\x -> (x, x+1))
  --   teleVarMap.at id .= Just (TeleVarInfo e Nothing)
  --   pure $ TeleTyVar id
  warn x = warnings <>= [OtherWarning x]
  blockMeta m c = fork (readMVar (_metaVal m) >>= c)
  -- blockMeta m c = readMeta m >>= \case
  --   Just v -> c v
  --   Nothing -> metaMap.at (coerce m)._Just %= (\(MetaInfo e t x l blx) -> MetaInfo e t x l (unsafeCoerce c:blx))


instance MonadScope ElabMonad where
  type ScopeSet ElabMonad n = [ScopeInfo n]
  newScope (e :: Env n) x = withKnownNat (envRecoverNat e) $
    pure [SimpleScope $ fromList $ fmap (\(x,y,z) -> (x,(y,z))) x]
  newScopeRec (e :: Env n) fs = do
    vr :: ScopeVar n <- ScopeVar <$> (idSupply %%= (\x -> (x, x+1)))
    let v = withKnownNat (envRecoverNat e) $ SolverScope (SNat @0) vr
    -- TODO: this needs to deal w/ blocking
    l <- traverse (\f -> f [v]) fs
    let l' = concat $ fmap fst l
        r = mconcat $ fmap snd l
    constraints <>= [DefineScope e vr l']
    pure ([v],r)
  lookupName b e s n = do
    (ty,ty') <- newTypeMeta b e
    (tm,tm') <- newMeta b e ty'
    constraints <>= [LookupName b e s n ty tm]
    pure (ty', coerce Ref n tm')

  -- go s
  -- where
    -- go (SimpleScope x:xs) = maybe (go xs) pure (x ^. at n)
    -- go (DelayedScope (_ :: _ m) x:xs) = do
    --   x' <- liftIO $ readMVar x
    --   maybe (go xs) ((pure . over (beside _Wrapped _Wrapped) (shiftN @_ @m @0))) (x' ^. at n)
    --   -- TODO: make metas if readMVar blocks here 
    -- go [] = error $ "unresolved name!: " <> show n
  wknScopes = fmap go where
    go (SimpleScope s) = SimpleScope $ fmap (over (beside _Wrapped _Wrapped) extendCore) s
    go (SolverScope (k :: _ k) (i :: _ n)) = withKnownNat (k %+ SNat @1) $
      gcastWith (assoc @n @k @1) $ SolverScope (SNat @(k + 1)) i
      where 
        assoc :: forall a b c. (a + b) + c :~: a + (b + c)
        assoc = unsafeCoerce Refl
  appendScopes = (<>)
  emptyScope = mempty

wknScopesN :: forall m n k. MonadScope m => Sing k -> ScopeSet m n -> ScopeSet m (n + k)
wknScopesN s x = case s %== SNat @0 of
  STrue -> unsafeCoerce x
  SFalse -> unsafeCoerce $ withKnownNat (s %- SNat @1) $ wknScopesN (s %- SNat @1) (wknScopes x)

-- idea: pass around (TeleTyVar, Type (n + 1)) & same for terms instead of using tele var lam & pi
-- uu(that works & is more reflective of how tele vars work)
-- like we have `data InferResult n = Princpial (Type n) (Term n) | WithTeleVar TeleTyVar (Type (n + 1)) (Term (n + 1))`
-- & elab passes that around instead of `Type n`

-- try_solve_constraint :: AConstraint -> ElabMonad Bool
-- try_solve_constraint c = case c of
--   -- Subtype bl e a b x m -> try_subtype bl e x y v
--   _ -> pure False

idT :: Type n -> Term n
idT ty = TermC $ Lam (TeleExplicitTy "x" (coerce ty) TeleEmpty) (bound finZ)

unifyMeta :: (MonadConstraints m, MonadCanUnify m) => Blame -> Env n -> MetaVar n -> Term n -> m ()
unifyMeta b e m x = readMeta m >>= \case
  Just v -> unify_ b e (coerce x) (coerce v)
  Nothing -> writeMeta m x

-- loop through all delayed constraints until no more get solved
-- shitty, slow, etc. temporary!
loop_solve :: ElabMonad ()
loop_solve = do
  cs <- use constraints
  if null cs then pure () else do
    constraints .= []
    go False cs
  where
  go p (x:xs) = f x >>= \case True -> go True xs; False -> (constraints <>= [x]) >> go p xs
  go True [] = loop_solve
  go False [] = pure ()
  f x = case x of
    Subtype b e x y v m -> do
      r <- try_subtype b e x y v
      case r of
        Just r' -> unifyMeta b e m r' >> pure True
        Nothing -> pure False
    Unify b e x y v m -> try_unify b e x y >>= \case
        Just True -> unifyMeta b e m v >> pure True
        Nothing -> pure False
    -- SubtypeTele bl e v a x b m -> try_subtypetele bl e v a x b >>= \case
    --     Just v' -> unifyMeta bl e m v' >> pure True
    --     _ -> pure False
    Unify_ b e x y -> try_unify b e (coerce x) (coerce y) >>= \case
        Just True -> pure True
        _ -> pure False
    LookupName b e s tx ty tm -> go s where
      go = \case
        [] -> pure False
        (SimpleScope m:sx) -> case m ^. at tx of
          Nothing -> go sx
          Just (ty',tm') -> unifyMeta b e ty (coerce ty') >> unifyMeta b e tm (coerce tm') >> pure True
        (SolverScope p v:sx) -> use (scopeMap . at (coerce v)) >>= \case
          Nothing -> pure False
          Just (Some (Compose s')) -> go (unsafeCoerce (wknScopesN p $ s') ++ sx)
    DefineScope e v s -> do
      Nothing <- use (scopeMap . at (coerce v))
      scopeMap.at (coerce v) .= Just (Some $ Compose s)
      pure True
    _ -> pure False



instance MonadCanUnify ElabMonad where
  readMeta m = tryReadMVar $ _metaVal m
  readMeta' m = readMVar $ _metaVal m
  writeMeta m v = writeMVar (_metaVal m) v
  -- writeMeta (m :: MetaVar n) v = do
  --   blx <- metaMap.at (coerce m)._Just %%= (\(MetaInfo e t x l blx) ->
  --     case x of
  --       Nothing -> (unsafeCoerce blx :: [Term n -> ElabMonad ()],MetaInfo e t (Just $ unsafeCoerce v) l [])
  --       Just v -> error "meta already solved!")
  --   for_ blx (\f -> f v)
  -- readMeta m = use (metaMap.at (coerce m)) >>= \case Just (MetaInfo _ _ mv _ _) -> pure $ unsafeCoerce mv
  -- metaTypeEnv m = use (metaMap.at (coerce m)) >>= \case Just (MetaInfo e ty _ b _) -> pure (b,unsafeReindex e,unsafeReindex ty)
  --   where unsafeReindex :: f x -> f y
  --         unsafeReindex = unsafeCoerce
  -- writeTeleVar t v = teleVarMap.at (coerce t).mapped %= (\(TeleVarInfo x Nothing) -> TeleVarInfo x (Just $ unsafeCoerce v))


    
 
-- TODO: is this still relevant now that we've removed tele var lam & pi?:
-- -- TODO: write up justifications for tele vars (over blocking etc)
-- -- list: MaxSMT, subterm property w/ holes, order-independence w/ parallel elaboration of e.g. top-level defs, more terms typecheck (consider: `f blargh` where `f :: Foo x a => a -> b`, blargh mentions x & constraint(s) from blargh on x cause Foo to be solved, which tells us the expected type of blargh, which tells us to insert implicit abstractions)

-- metaInfo :: MetaVar n -> ElabMonad MetaInfo
-- metaInfo m = maybe undefined id <$> use (metaMap . at (coerce m))


-- -- IntSet is assumptions
-- newtype AssumptionT m a = AssumptionT { runAssumptionT :: StateT (MHashMap Int IntSet, IntSet) m a }
--   deriving (MonadTrans, Functor, Applicative, Monad)


-- instance MonadCanUnify m => MonadCanUnify (AssumptionT m) where
--   readMeta m = AssumptionT $ do
--     as <- maybe undefined id <$> use (_1.at (coerce m))
--     _2 <>= as
--     lift $ readMeta m
--   writeMeta m v = AssumptionT $ do
--     as <- use _2
--     _1.at (coerce m) <>= Just as
--     lift $ writeMeta m v


-- newtype ScopeSetA m n = ScopeSetA (ScopeSet m n)
--
-- instance MonadMeta m => MonadMeta (AssumptionT m) where
--   newMeta b e t = lift $ newMeta b e t
--   newTypeMeta b e = lift $ newTypeMeta b e
-- instance (MonadScope m) => MonadScope (AssumptionT m) where
--   type ScopeSet (AssumptionT m) n = ScopeSetA m n
--   newScope e s = lift $ coerce <$> newScope e s
--   newScopeRec e s = AssumptionT $ do
--     st <- get
--     (ss,(r,st')) <- lift $ newScopeRec e $ fmap
--       (\f x -> (\((a,b),c) -> (coerce a,(b,c))) <$> (runStateT . runAssumptionT) (f (coerce x)) st) s
--     put st'
--     pure (coerce ss,r)
--   lookupName b e s n = lift $ lookupName b e (coerce s) n
--   wknScopes (ScopeSetA ss) = coerce $ wknScopes ss
--   appendScopes (ScopeSetA a) (ScopeSetA b) = coerce $ appendScopes a b
--   emptyScope = ScopeSetA emptyScope
-- instance MonadConstraints m => MonadConstraints (AssumptionT m) where
--   subtype b e x y v = lift $ subtype b e x y v
--   subtypeTele b e r t = lift $ subtypeTele b e r t
--   newTeleVar e = lift $ newTeleVar e

-- newtype TacticM a = TacticM { runTacticM :: StateT  }
