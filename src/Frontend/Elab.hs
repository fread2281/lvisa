{-# LANGUAGE OverloadedLists, ScopedTypeVariables, AllowAmbiguousTypes, BlockArguments #-}
{-# OPTIONS_GHC -Wno-tabs #-}
module Frontend.Elab where


import Solver.MonadTac
import Solver.MonadTacImpl
import Solver.MonadTacTypes
import qualified Frontend.Expr as E
import Frontend.Expr (Spanned(..),Expr')
import Frontend.Parser
import Frontend.Indentation
-- import Control.Concurrent.MVar
import Core
import Lib.Fin
-- import GHC.TypeLits
import Text.Parsix (Span(..),Result(..),prettyError,eof,anyChar,parseText)
import qualified Text.PrettyPrint.ANSI.Leijen as P
import Control.Monad.Cont
import Data.Singletons.Prelude.Num
import Data.Singletons.TypeLits
import Data.Singletons.Prelude.Bool
import Data.Singletons.Prelude.Eq
import Data.Singletons.Decide
import Solver.Unify
import Solver.Class

-- so here's how tele vars work
-- * points for insertion of implicit lam if typechecking tells us something should have one (is of type implicit pi)
-- * (TODO) points for implicit let-generalization (insertion of implicit pi)
-- due to second tele vars are of 'type' another tele var (TODO: huh?)
-- tele vars are telescopes which might contain pis or lambdas

-- TODO: for let-gen, we need to be able to know when a meta var won't become more solved

-- catchWarn :: MonadConstraints m => m () -> m ()
-- catchWarn x = _ -- liftIO _

lam :: Telescope n m -> Core (n + m) -> Core n
lam TeleEmpty x = x
lam t x = withKnownNat (teleRecoverNat t) $ Lam t x



elabInfer :: MonadConstraints m => Env n -> ScopeSet m n -> Expr' -> m (Type n, Term n)
-- elabInfer e s x | trace (show $ "elabInfer: " <> pretty e <> " |- " <> pretty x) False = undefined
elabInfer e s (E.Var i :~ b) = lookupName (Blame ("lookupName " ++ unpack i) b) e s i
elabInfer e s (E.Lam [] b :~ _) = elabInfer e s b
elabInfer e s x@(_ :~ l) = do
  (_,tyM) <- newTypeMeta (Blame "elabInfer ty" l) e
  (_,tmM) <- newMeta (Blame "elabInfer tm" l) e tyM
  fork $ un_implicit_pi tyM $ \tele tyE -> do
    let e' = appEnvTele e tele
    (tyI, tmI) <- go e' (wknScopesN (teleRecoverNat tele) s) x
    TermC tmC <- unify (Blame "elabInfer ty coe" l) e' tyI tyE tmI
    unify_ (Blame "elabInfer tm eq" l) e (coerce tmM) (withKnownNat (teleRecoverNat tele) $ lam tele tmC) --(coerce tmC) (Lam tele _)
  pure (tyM, tmM)
  where
    go :: forall m n. MonadConstraints m => Env n -> ScopeSet m n -> Expr' -> m (Type n, Term n)
    go e s (E.Var i :~ b) = lookupName (Blame ("lookupName " ++ unpack i) b) e s i
    go e s (E.Arr x y :~ b) = go e s (E.Pi [(b,E.Explicit,"",x)] y :~ b)
    go e s (E.Pi t x :~ _) = typeToTerm <$> go2 e s t x where
      go2 :: forall n m. MonadConstraints m => Env n -> ScopeSet m n -> [(Span,E.Plicitness,Text,Expr')] -> Expr' -> m (Level n, Type n)
      go2 e s [] a = elabType e s a
      go2 e s ((l,p,v,ty):xs) a = do
        tyR@(_,ty'@(TypeC tyV)) <- elabType e s ty
        let e' = (SnocEnvTy e v ty')
        s' <- newScope e' [(v,TypeC $ extendCore tyV, TermC $ bound finZ)]
        rs <- go2 e' (s' `appendScopes` wknScopes s) xs a
        pure $ (case p of E.Explicit -> makePi; E.Implicit -> makeImplicitPi) v tyR rs
    go e s (E.Lam ((l,v,ty):xs) b :~ p) = do
      ty'@(TypeC tyV) <- elabTypeMaybe e s ty p
      let e' = SnocEnvTy e v ty'
      s' <- newScope e' [(v,TypeC $ extendCore tyV, TermC $ bound finZ)]
      -- TODO: pass smaller loc here!
      rs <- elabInfer e' (s' `appendScopes` wknScopes s) (E.Lam xs b :~ p)
      pure $ makeLam v ty' rs
    go e s (E.Lam [] b :~ _) = go e s b
    go e s (E.Underscore :~ l) = do
      (_,ty) <- newTypeMeta (Blame "underscore" l) e
      (_,tm) <- newMeta (Blame "underscore" l) e ty
      pure (ty,tm)
    go e s (E.App l :~ b) = f =<< traverse (elabInfer e s) l where
      f [x] = pure x
      f (x:y:xs) = app (Blame "app" b) e x y >>= (f . (:xs))
    -- TODO: case should take an argument, like
    -- case : Generic a => a -> Macro
    go e s (E.MacroE (E.MacroCall (E.Var "case" :~ _) (Just x)) :~ l) = do
      p <- parseM ((,) <$> expr <* lift "of" <*> block (many ((,) <$> some (spanned (flip (:~)) word) <* "->" <*> hanging expr)) <* eof) x
      case p of
        Just (v,cases) -> do
          -- TODO: this doesn't infer/check (need to require ty ~ cty args)
          v'@(ty,TermC val) <- elabInfer e s v
          (_,r) <- newTypeMeta (Blame "case ret" l) (SnocEnvTy e "" ty)
          let rty = coerce subst1 val r
          (m :: MetaVar n1,rtm) <- newMeta (Blame "case val" l) e rty
          fork $ do
            v <- for cases (\(lhs,rhs) -> do
              -- TODO: support default cases (if lhs = just one var & not a constructor)
              let (c,args) = (head lhs,tail lhs)
              (cty,ctm) <- elabInfer e s (E.Var <$> c)
              Constructor con <- whnf_block $ coerce ctm
              un_pi (coerce cty) $ \tele rty -> do
                -- len args' + p = len tele
                let go2 :: forall o p. KnownNat o => Env (n1 + o) -> ScopeSet m (n1 + o) -> Telescope (n1 + o) p -> [Spanned Text] -> [Core (n1 + o)]-> m (CaseAlt n1)
                    go2 e s (TeleExplicitTy n ty r) ((vn :~ _):xs) args' = gcastWith (assoc @n1 @o @1) $ do
                      let e' = SnocEnvTy e vn (TypeC ty)
                      s' <- newScope e' [(vn,TypeC $ extendCore ty,TermC $ (bound finZ :: Core (n1 + o + 1)))]
                      withKnownNat (SNat @o %+ SNat @1) $
                        go2 @(o + 1) e' (s' `appendScopes` wknScopes s) r xs (fmap extendCore args' ++ [bound finZ])
                    go2 e s TeleEmpty [] args' = do
                      rhs' <- elabCheck e s rhs (coerce subst1 (App (shiftN @n1 @o @0 $ coerce ctm) $ fromList args') $ shiftN @n1 @o @1 $ coerce r)
                      pure $ CaseAlt con (SNat @o) $ coerce rhs'
                go2 @0 e s tele args []
              )
            writeMeta m $ TermC $ Case ty val r v
          pure (rty,rtm)
        _ -> do
          (_,ty) <- newTypeMeta (Blame "bad case statement" l) e
          (_,tm) <- newMeta (Blame "bad case statement" l) e ty
          pure (ty,tm)
    go e s (E.Parens x :~ _) = go e s x
    go e s x = error $ "elabInfer nyi: " <> show x

    -- go e s (E.Arr a b :~ _) = _
    -- go e s (E.Lam t x :~ _) = go2 e s t x where
    --   go2 :: Env n -> [ScopeSet ElabMonad n] -> [E.TelescopeElem Text] -> Expr' -> ElabMonad (Type n, Term n)
    --   go2 e s [] a = elabInfer' e s a
      -- go2 e s (E.ExplicitAnn l v ty:xs) a = do
      --   _


elabCheck :: MonadConstraints m => Env n -> ScopeSet m n -> Expr' -> Type n -> m (Term n)
elabCheck e s x@(_ :~ l) t = do
  (ty,tm) <- elabInfer e s x
  unify (Blame "elabCheck" l) e t ty tm

elabType :: MonadConstraints m => Env n -> ScopeSet m n -> Expr' -> m (Level n, Type n)
elabType e s x@(_ :~ l) = do
  (_,TermC lvl) <- newMeta (Blame "elabType" l) e (TypeC $ ConstC Level)
  TermC tm <- elabCheck e s x (TypeC $ Type lvl)
  pure (LevelTerm lvl, TypeC tm)

-- elabInfer e s (E.Var i :~ b) = lookupName (Blame "lookupName" b) e s i
-- elabInfer e s (E.App a b :~ l) = do
--   -- TODO: should infer one then check the other, which order?
--   -- TODO: need to insert tele vars here maybe?
--   b' <- elabInfer e s b
--   a' <- elabInfer e s a
--   app (Blame "app" l) e a' b'
-- elab e s (Lam t x :~ _) = go e s t x
--   where
--     go :: (MonadElab m, MonadScope m) => Env n -> [Scope m n] -> [TelescopeElem Text] -> Expr' -> m (Type n, Term n)
--     go e s [] v = elab e s v
--     go e s (ExplicitAnn l v ty:xs) x = do
--       -- TODO: insert implicits
--       -- need to refactor so it can modify e while inserting implicits probably
--       -- :(

--       (tyL,ty') <- elab e s ty >>= assertIsType (Blame "lam" l) e
--       rs <- go (SnocEnv e ty') (fmap wknScope s) xs x
--       pure $ makeLam v ty' rs

parseM :: MonadConstraints m => Parser a -> (Span,Text) -> m (Maybe a)
parseM p (Span a _,inp) = case parseTextRel p inp "<macro>" a of
  Success a -> pure $ Just a
  Failure f -> do
    warn $ P.text $ show $ prettyError f
    pure Nothing

un_pi :: forall n mo r. MonadConstraints mo => Core n -> (forall o. KnownNat o => Telescope n o -> Core (n + o) -> mo r) -> mo r
un_pi x c = whnf_block x >>= \case
  Pi (t :: Telescope _ m) b -> un_pi b $ \(t2 :: Telescope _ o) b2 ->
    withKnownNat (SNat @m %+ SNat @o) $ c (appendTele t t2) (gcastWith (assoc @n @m @o) b2)
  x -> c TeleEmpty x
  -- x -> error $ "nyi un_pi: " <> show x

whnf_block :: forall n m. MonadConstraints m => Core n -> m (Core n)
whnf_block x = whnf x >>= \case
  (True,r) -> pure r
  (False,Meta m s) -> do
    v <- readMeta' m
    whnf_block (subst s $ coerce v)

-- -- like mtac's `nu (fun x => abs_fun x body)` but for pi instead of lam
-- -- the variable can't be used in unification, so this is limited
-- -- eventually there'll be a fanicer version in a tactic monad
-- -- that puts the var in the env & works with unification
-- piM :: Text -> Core n -> (Core n -> ContT () ElabMonad (Core n)) -> ContT () ElabMonad (Core n)
-- piM n ty f = do
--   id <- idSupply %%= (\x -> (x, x+1))
--   Pi (TeleExplicitTy n ty TeleEmpty) . subst (SubstFree id (bound finZ)) . extendCore <$> f (Free id)

arr :: Core n -> Core n -> Core n
arr x y = Pi (TeleExplicitTy "" x TeleEmpty) (extendCore y)

elabTypeMaybe :: MonadConstraints m => Env n -> ScopeSet m n -> Maybe Expr' -> Span -> m (Type n)
elabTypeMaybe e s ty p = case ty of
  Just ty -> snd <$> elabType e s ty
  Nothing -> snd <$> newTypeMeta (Blame "elabTypeMaybe" p) e

elabDefinitions :: forall n m. (MonadConstraints m, m ~ ElabMonad) => Env n -> ScopeSet m n -> [(E.Definition,Span)] -> m (ScopeSet m n)
elabDefinitions e s ds = 
  fmap fst $ newScopeRec e $ ds <&> \d s' -> (,()) <$> case d of
    (E.Definition n Nothing ty val,l) -> do
      ty' <- elabTypeMaybe e (s' `appendScopes` s) ty l
      val' <- elabCheck e (s' `appendScopes` s) val ty'
      newScope e [(n,ty',val')]
    (E.MacroD (E.MacroCall (E.Var "data" :~ _) (Just x)),l) -> do
      let sig = (,) <$> word <* ":" <*> hanging expr      
      p <- parseM ((,) <$> sig <* lift "where" <*> block (many sig) <* eof) x
      case p of
        Nothing -> pure emptyScope
        Just ((nm,ty),cs) -> do
          id <- idSupply %%= (\x -> (x, x+1))
          -- FIXME: actually check ty' ends in Type & constrs end in ty'
          (_,ty') <- elabType e (s' `appendScopes` s) ty
          sty <- newScope e [(nm,ty',TermC $ Constructor $ DataCon nm id $ coerce ty')]
          let s'' = sty `appendScopes` (s' `appendScopes` s)
          cs' <- for cs $ \(n,xr) -> do
            id' <- idSupply %%= (\x -> (x, x+1))
            (\(_,t) -> (n,t,TermC $ Constructor $ DataCon n id' $ coerce t)) <$> elabType e s'' xr
          scs <- newScope e cs'
          -- TODO: make match principle
          -- Nat_match : (x : Nat) -> ((y : Nat) -> x = S y => r) -> (x = Z => r) -> r
          -- Nat_match : (P : Nat -> Set) -> ((y : Nat) -> P (S y)) -> P Z -> (x : Nat) -> P x
          -- 
          -- match_ty <- newTypeMeta (Blame "match" l) e
          -- un_pi (coerce ty') $ \(t,Type l) -> runContT (do
          --   let p = Pi t (arr _ _)
          --   piM "P" p _
          --   ) _
            -- runContT (itraverse _ cs') _
          -- (tele,Type n) <- un_pi sty
          -- 
          -- let match_ty = [term|(P : [pi_tele tele [term|Type]]) -> [pi_list $ fmap _ constrs] -> [pi_tele tele (P [0..length tele-1])]]
          -- 
          -- 
          -- let gen_match 
          pure $ appendScopes scs sty
    (E.MacroD (E.MacroCall (E.Var m :~ b) _),l) -> do
      warn $ "Unknown macro: " <> pretty m <> " at " <> pretty b
      pure emptyScope



