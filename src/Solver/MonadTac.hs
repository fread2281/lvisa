{-# LANGUAGE OverloadedLists, TypeFamilyDependencies, GeneralizedNewtypeDeriving, ScopedTypeVariables, InstanceSigs #-}
-- | 

module Solver.MonadTac where

-- import Control.Applicative
import GHC.TypeLits hiding (Text)
import Core
import Solver.MonadTacTypes
import GHC.Stack (HasCallStack)
import Frontend.Expr (Plicitness)
import Control.Monad.Fail
import Solver.Class

typeToTerm :: (Level n, Type n) -> (Type n, Term n)
typeToTerm (LevelTerm lvl, TypeC t) = (TypeC $ Type lvl, TermC t)

makeImplicitPi :: Text -> (Level n, Type n) -> (Level (n + 1), Type (n + 1)) -> (Level n, Type n)
makeImplicitPi n (LevelTerm xl,TypeC x) (LevelTerm yl,TypeC y) = (LevelTerm $ App (ConstC LSup) [xl,x,Lam t2 yl], TypeC $ Pi t y)
  where t = TeleImplicitTy n x TeleEmpty
        t2 = TeleExplicitTy n x TeleEmpty

makePi :: Text -> (Level n, Type n) -> (Level (n + 1), Type (n + 1)) -> (Level n, Type n)
makePi n (LevelTerm xl,TypeC x) (LevelTerm yl,TypeC y) = (LevelTerm $ App (ConstC LSup) [xl,x,Lam t yl], TypeC $ Pi t y)
  where t = TeleExplicitTy n x TeleEmpty

-- lsup :: 

makeLam :: Text -> Type n -> (Type (n + 1), Term (n + 1)) -> (Type n, Term n)
makeLam n (TypeC x) (TypeC ty,TermC tm) = (TypeC $ Pi t ty, TermC $ Lam t tm)
  where t = TeleExplicitTy n x TeleEmpty


-- TODO: need to figure out how implicit lambda insertion works w/o tele vars

-- idea: only expose check, not infer
-- & check is builtin
-- (infer is not exported, internally can be whatever, check=>infer can know about tele vars)
-- how do macros ask for tele vars or equiv?
-- they should just use the builtin points where tele vars are inserted
-- & that should be sufficient for now
-- TODO: smart constructors for terms should insert implicit insertion points i think???
-- (like `app x y` => `\{_v} -> x {_w} y`)
-- TODO: should be able to skip if returned term is principal/has no holes
-- TODO: decide when/if tele vars can contain explicits

-- TODO: make this nicer...
app :: MonadConstraints m => Blame -> Env n -> (Type n, Term n) -> (Type n, Term n) -> m (Type n, Term n)
app l e a@(_,TermC av) (bty@(TypeC btyv),TermC bv) = do
  (_,TypeC cod) <- newTypeMeta l (SnocEnvTy e "" bty)
  TermC fn <- subtype l e (fst a) (TypeC (Pi (TeleExplicitTy "" btyv TeleEmpty) cod)) $ TermC av
  pure (TypeC (subst1 bv cod), TermC (App fn [bv]))


-- TODO: 
-- * weights
-- * make sure our api works for typeclasses
-- * switch to ~coq-style levels
-- TODO: could we make Blame implicit by default? (just macro src loc or something?)
-- TODO: add unify?
class Monad m => MonadMeta m where
  newTypeMeta :: Blame -> Env n -> m (MetaVar n, Type n)
  newMeta :: Blame -> Env n -> Type n -> m (MetaVar n, Term n)
  -- -- directed coercion (might insert implicit aplications or abstractions)
  -- coeTy :: Blame -> Env n -> Type n -> Type n -> m (Term n)
  -- TODO: ?
  -- this should be derived from coe and el when we're typed
  -- (`el : Term e (type l) -> Type e`)
  -- assertIsType :: Blame -> Env n -> (Type n, Term n) -> m (Level n, Type n)


-- question: can blocking on metas instead of tele vars or w/e sometimes avoid an occurs check??

-- TODO: clean this up & move it, once MetaVar is parameterized by n
-- this is here just so that unify can work on a MonadCanUnify & therefore
-- can share unify between fast solving & error localization
-- should move to more internal module
class (MonadMeta m,  MonadFail m) => MonadCanUnify m where
  readMeta :: MetaVar n -> m (Maybe (Term n))
  -- blocks
  readMeta' :: MetaVar n -> m (Term n)
  -- metaTypeEnv :: MetaVar n -> m (Blame, Env n, MetaType n)
  writeMeta :: HasCallStack => MetaVar n -> Term n -> m ()

-- class MonadMeta m => MonadTac m where
--   -- | coe _ _ a b x, given x : a, returns y : b
--   coe :: Blame -> Env n -> Type n -> Type n -> Term n -> m (Term n)

-- TODO: refactor this?
-- all the constraints, internal for now
class (MonadMeta m, MonadScope m, MonadFail m, MonadCanUnify m, MonadIO m, MVish m) => MonadConstraints m where
  subtype :: Blame -> Env n -> Type n -> Type n -> Term n -> m (Term n)
  -- subtypeTele :: Blame -> Env n -> InferResult n -> Type n -> m (Term n)
  unify :: Blame -> Env n -> Type n -> Type n -> Term n -> m (Term n)
  unify_ :: Blame -> Env n -> Core n -> Core n -> m ()

  warn :: Doc -> m ()

  blockMeta :: MetaVar n -> (Term n -> m ()) -> m ()




-- class MonadBacktrack m where
--   -- take first if possible, else take second
--   biasedAlt :: m a -> m a -> m a
--   -- take first if not second, second if not first
--   -- if both, take the first and warn (TODO: ?)
--   unbiasedAlt :: m a -> m a -> m a

-- TODO APIs:
-- warnings
-- what else?

-- TODO: move MonadScope to low-level non-exported
-- w/ MonadCanUnify
-- TODO: (forall n. Monoid (ScopeSet m n)) =>
-- once QuantifiedConstraints actually works
class (Monad m) => MonadScope m where
  -- TODO: s/ScopeSet/Scope/ ?
  -- | NOTE: ScopeSet is left-biased, i.e. if a and b both define `name`, `a <> b` will prefer a's `name`
  type ScopeSet m (n :: Nat) = r | r -> n m
  newScope :: Env n -> [(Text, Type n, Term n)] -> m (ScopeSet m n)
  -- letrec! need the complex type for letrec + macros, see decisions.md
  newScopeRec :: Monoid r => Env n -> [ScopeSet m n -> m (ScopeSet m n, r)] -> m (ScopeSet m n, r)
  lookupName :: Blame -> Env n -> ScopeSet m n -> Text -> m (Type n, Term n)
  -- TODO: blame
  -- `assignName e s (ty,val)`, requires `val : ty`
  -- TODO: do we need to worry about tele vars here?
  wknScopes :: ScopeSet m n -> ScopeSet m (n + 1)

  -- here until QuantifiedConstraints actually works
  appendScopes :: ScopeSet m n -> ScopeSet m n -> ScopeSet m n
  emptyScope :: ScopeSet m n



-- TODO: spanned text type & parser combinators

-- class (MonadTac m, MonadScope m) => MonadElab m where
  -- elab :: Env n -> [ScopeLookup m n] -> (Text,Span) -> Type n -> m (Term n)
