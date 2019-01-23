{-# LANGUAGE ScopedTypeVariables, TypeApplications, OverloadedLists, AllowAmbiguousTypes, PatternSynonyms, DerivingVia #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
module Solver.Unify where


import Solver.MonadTac
import Solver.MonadTacTypes
import Core
import Lib.Fin
import Control.Monad.Trans.Maybe
import Data.Monoid
import qualified Data.Sequence as S
import Data.Singletons.Prelude.Num
import Data.Singletons.Prelude.Bool
import Data.Singletons.Prelude.Ord hiding (Max)
import Data.Singletons.Prelude.Eq
import Data.Singletons.Decide
import Data.Singletons.TypeLits hiding (natVal)
-- import Data.Validation

-- try to normalize to whnf,
-- bool is if result is in whnf
whnf :: MonadCanUnify m => Core n -> m (Bool, Core n)
whnf x = coerce <$> go x where
  go :: MonadCanUnify m => Core n -> m (Max Bool, Core n)
  go x = case x of
    Constructor _ -> ok
    Bound _ -> ok
    Meta m s -> readMeta m >>= \case
      Just v -> go $ subst s $ coerce v
      Nothing -> no
    App (ConstC _) _ -> ok
    -- Core.Subst s x' -> case subst s x' of
    --   y@(Core.Subst _ _) -> pure (Max False, y)
    --   v -> go v
    Pi _ _ -> ok
    -- TODO: ?
    Ref n x -> go x
    -- _ -> no
    where
      ok = pure (Max True, x)
      no = pure (Max False, x)

-- get rid of known metas
zonk_term :: MonadCanUnify m => Core n -> m (Core n)
zonk_term = go where
  go :: MonadCanUnify m => Core n -> m (Core n)
  go x = case x of
    Bound _ -> pure x
    Meta m s -> readMeta m >>= \case
      Just v -> go $ subst s $ coerce v
      Nothing -> pure x
    App a bs -> App <$> go a <*> traverse go bs
    Pi t x -> Pi <$> go_tele t <*> go x
    Lam t x -> Lam <$> go_tele t <*> go x
    -- Subst s x -> subst s <$> go x
    Constructor (DataCon n i x) -> Constructor . DataCon n i <$> go x
    _ -> pure x

  go_tele :: MonadCanUnify m => Telescope a b -> m (Telescope a b)
  go_tele TeleEmpty = pure TeleEmpty
  go_tele (TeleExplicitTy n x r) = TeleExplicitTy n <$> go x <*> go_tele r
  go_tele (TeleImplicitTy n x r) = TeleImplicitTy n <$> go x <*> go_tele r

-- -- normalize, returns as soon as it can't become in the pattern fragment
-- whnfSubst :: MonadCanUnify m => Subst a b -> m (Subst a b)
-- whnfSubst (ASubst x SI) = pure (ASubst x SI)
-- whnfSubst (ASubst s w@(SC (j@SNat :: Sing j) r x)) = whnf r >>= \case
--   (_, Bound v) -> whnfSubst (ASubst (S (maybe (invSC j x v) id . finMidSplit @_ @1 @j) . s) (f j x))
--   (_,r') -> pure (ASubst s (SC j r' x))
--   where
--     f :: Sing j -> SC i j r -> SC (i + j) 0 r
--     f j SI = SI
--     f j (SC w r x) = SC (w %+ j) r x

-- figure out if ty might start with an implicit pi
-- might use backtracking or block internally
-- 
-- actually, it blocks & uses backtracking if we don't have enough to do (some threads are work-starved)
-- (guesses it doesn't start w/ implicit pi, backtracks if it does and then
-- guesses whatever it started with (when we assumed it didn't start with anything))
un_implicit_pi :: MonadConstraints m => Type n -> (forall o. Telescope n o -> Type (n + o) -> m r) -> m r
-- FIXME: this is a hack, assuming no implicit pis
un_implicit_pi x r = r TeleEmpty x 


-- work on unifying two things.
-- returns true if they've been unified, false if they're not unifiable
-- and nothing if the problem needs to be postponed
try_unify :: forall m n. MonadCanUnify m => Blame -> Env n -> Type n -> Type n -> m (Maybe Bool)
try_unify b = coerce f where
  f :: forall n. Env n -> Core n -> Core n -> m (Maybe Bool)
  -- f e x y | trace ("unify: " <> show x <> " ~ " <> show y) False = pure Nothing
  f e (Ref n a) (Ref m b) = if n == m then f e a b else pure Nothing
  f e (ConstC a) (ConstC b) = pure $ Just $ a == b
  f e (Constructor (DataCon _ i _)) (Constructor (DataCon _ j _)) = pure $ Just $ i == j
  f e (Bound a) (Bound b) = pure $ Just $ (a == b)
  f e (App (ConstC a) as) (App (ConstC b) bs) | a == b = fmap and . sequenceA <$> sequenceA (S.zipWith (f e) as bs)
  f e (Pi t x) (Pi t' x') = f_tele e t t' >>= \case
    Just True -> f undefined x $ unsafeCoerce x'
    _ -> pure Nothing
  -- TODO: is this good/right?
  f e a@(Meta m s) b@(Meta n t) = f_meta e m s b >>= \case
    Just r -> pure $ Just r
    Nothing -> f_meta e n t a
  f e (Meta m s) b = f_meta e m s b
  f e a (Meta m s) = f_meta e m s a
  f e (Ref n a) b = f e a b
  f e a (Ref n b) = f e a b
  f e x y | trace ("unify nyi: " <> show x <> " ~ " <> show y) True = pure Nothing

  f_meta :: forall n o. Env n -> MetaVar o -> Subst o n -> Core n -> m (Maybe Bool)
  f_meta e m s b = readMeta m >>= \case
        Just v -> f e b (subst s $ coerce v)
        Nothing -> 
          withKnownNat (envRecoverNat $ _metaEnv m) $
          case invert s of
            Just si -> pruneTm si b >>= \case
              Just b' -> do
                writeMeta m $ coerce b'
                pure $ Just True
              Nothing -> pure Nothing
            Nothing | trace ("inversion failed: " <> show b <> " ~ " <> show (Meta m s)) True -> pure Nothing

  f_tele :: forall n o p. Env n -> Telescope n o -> Telescope n p -> m (Maybe Bool)
  f_tele e (TeleExplicitTy t c x) (TeleExplicitTy _ c' x') = f e c c' >>= \case
    Just True -> f_tele (SnocEnvTy e t $ TypeC c) x x'
    _ -> pure Nothing
  f_tele e TeleEmpty TeleEmpty = pure $ Just True

  -- f e (App' (Meta m) as) b = undefined
  -- f e b (App' (Meta m) as) = do

try_subtype :: forall m n. (MonadConstraints m, MonadCanUnify m) => Blame -> Env n -> Type n -> Type n -> Term n -> m (Maybe (Term n))
try_subtype b = go
  where
  go e (TypeC x) (TypeC y) v = do
    (xn,x') <- whnf x
    (yn,y') <- whnf y
    let t = fromMaybe True . is_implicit_pi
    -- TODO: this is wrong, should be backtracking
    -- (hacky, temporary)
    -- but uh type inference + subtyping is hard, so this is needed until i figure that out ...
    -- backtracking would be less bad though, but still hacky
    if (xn || yn) -- && not (t x' || t y')
     then Just <$> unify b e (coerce x') (coerce y') v
     else pure Nothing

-- try_subtypetele :: forall m n. (MonadCanUnify m, MonadConstraints m) => Blame -> Env n -> TeleTyVar n -> Type (n + 1) -> Term (n + 1) -> Type n -> m (Maybe (Term n))
-- try_subtypetele b e t x v (TypeC y) = do
--   (yn,y') <- whnf y
--   if yn && not (fromMaybe True $ is_implicit_pi y')
--   then do
--     writeTeleVar t TeleEmpty
--     Just <$> subtype b e (coerce (substTele0 @_ @0) x) (coerce y) (coerce (substTele0 @_ @0) v)
--   else pure Nothing

-- try to apply a partial subst to a term, pruning if needed
pruneTm :: forall m n o. MonadCanUnify m => (Fin n -> [Fin o]) -> Core n -> m (Maybe (Core o))
pruneTm s x = getCompose $ traverseSubst g f x where
  f :: forall j k. Sing j -> MetaVar k -> Subst k (n + j) -> (Compose m Maybe) (Core (o + j))
  f SNat mv ms = Compose $
    readMeta mv >>= \case
      Just val -> pruneTm (splitFin @_ @j (over each (finSn @j) . s) (pure . weakenFin)) $ subst ms $ coerce val
      Nothing -> do
        let bl = _metaSource mv
            env = _metaEnv mv
            ty = _metaType mv
        prune env ms (splitFin @n @j (fmap (finSn @j) . s) (pure . weakenFin @j @o)) (pure Nothing) $ \f sf ps sln ->
          -- case envRecoverNat f %~ envRecoverNat env of
          --   Proved Refl -> pure $ Just $ Meta mv ms
          --   _ -> 
              do
              let bl' = case bl of Blame x y -> Blame (x ++ " p") y
              tm :: Term _ <- case ty of
                IsType -> coerce . snd <$> newTypeMeta bl' f
                HasType tyx -> do
                  Just ty' <- pruneTm (\x -> maybe [] pure $ ps x) $ coerce tyx
                  snd <$> (newMeta bl' f $ coerce ty')
              writeMeta mv (coerce subst sf tm)
              pure $ Just $ subst sln $ coerce tm
  g :: Bool -> Fin n -> Compose m Maybe (Core o)
  g rigid v = Compose $ pure $ case s v of
    [r] -> Just $ Bound r
    -- TODO: error if rigid, delay if not
    _ -> Nothing


newtype One a = One' { getOne :: Ap Maybe (Maybe a) }
  deriving Applicative via (Compose (Ap Maybe) Maybe)
  deriving Functor via (Compose (Ap Maybe) Maybe)

pattern Many = One' (Ap Nothing)
pattern One a = One' (Ap (Just (Just a)))
pattern Zero = One' (Ap (Just Nothing))

-- apply a partial substn to a meta, pruning it & normalizing the env
--
-- we unconditionaly prune,
-- since pruning might cause other stuff to unblock
-- -- for all vars in `im s`:
-- -- any are Term => return nothing
-- -- each NoOcc => prune that var from p
-- -- any are OccVars length > 1 => return nothing
prune :: forall n m o r. Env m -> Subst m n -> (Fin n -> [Fin o]) -> r ->
    (forall p. KnownNat p => Env p -> Subst p m -> (Fin m -> Maybe (Fin p)) -> Subst p o -> r) -> r
-- prune _ _ _ x _ = x
prune EmptyEnv s p _ c = c EmptyEnv id Just (Subst $ \_ -> error "absurd: Fin 0")
prune (SnocEnvTy (e :: Env n2) n ty) (Subst s) f cn c = 
  let x' = s (finZ :: Fin (n2 + 1)) & traverseSubst (\rv -> (\case [v] -> One $ Bound v; [] -> if rv then Zero else Many; _ -> Many) . f) (\_ _ _ -> Many) in
    prune e (Subst s . Subst (extendCore . Bound)) f cn $ \(g :: Env p) sg sx d -> case x' of
      One y -> case traverseSubst (\rv -> maybe (if rv then Zero else Many) pure . fmap Bound . sx) (\_ _ _ -> Many) (coerce ty) of
        One ty' -> c (SnocEnvTy g n $ coerce ty') (substSkip (SNat @1) sg) (splitFin @_ @1 (fmap finSucc . sx)
          (\_ -> Just $ maxFin $ SNat @p)) (substAt1 y d)
        Zero -> c g (substExtend  . sg) (splitFin @_ @1 sx (const Nothing)) d
        Many -> cn
      Zero -> c g (substExtend . sg) (splitFin @_ @1 sx (const Nothing)) d
      Many -> cn
-- prune _ _ _ x _ | trace "prune failed" True = x


invert :: KnownNat a => Subst a b -> Maybe (Fin b -> [Fin a])
invert (Subst s) = getAp $ ifoldMap f $ FiniteFun s where
  f :: Fin a -> Core b -> Ap Maybe (Fin b -> [Fin a])
  f a (Bound b) = pure $ \x -> if x == b then [a] else []
  f _ _ = mempty

-- invert :: forall n m. KnownNat n => S n m -> BoundV m -> [BoundV n]
-- invert (S s) = flip ifoldMap (FiniteFun s) $ \f x -> case x of
--   Left y -> \y' -> if y' == y then [BoundV f Nothing] else []
--   Right (SV k s') -> withKnownNat k $ invert s' & fmap (fmap (\x -> BoundV f $ Just (BoundT k x)))








-- unification is somewhat global, do we want that??
-- no global unification(/backtracking??) by default, but allow like mutual blocks that allow unification inside them
-- so bookeeping for vars is what unification scope it came from
-- & we warn if it gets solved due to equations from different scope




-- here's how MaxSMT's gonna work:
-- - heirarchical version of the machinery in practical SMT-based error localization. typecheck as much as possible w/o maxsmt (use that machinery to reuse normally inferred types)
--   i think: when breaking file into bits, do `var_file = and vars_bits`. semantics is var_file is "depends on the known types from file, or depends on at least one thing from file"
--   i think: use the polymorphism machinery for tele vars that get solved w/ most general soln to set of constraints (our equiv to normal let-generalization). duplicate constraints & replace w/ eagerly-solved tele var
--   reason for the machinery around polymorphism is to determine what part of a function is causing type error
--   & to be able to use use-sites of function to put weight on subterms of function, to get more precise data on which constraints are most important
-- - unification impl that keeps track of assumption variables, keeps variable values and checks if assumptions are same as last run & uses them to generate conflict caluses for maxsat
-- - call external maxsat w/ cegar that does principal types & unification
-- 




-- data Maybe2 a = Good | Bad | Changed a
--   deriving (Functor)




-- traverseMaybe2 :: Monad f => (a -> f (Maybe2 a)) -> a -> f a
-- traverseMaybe2 
-- instance Applicative (Maybe2 a) where
--   Good f <*> Good x = 
