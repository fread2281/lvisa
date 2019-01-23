-- | Some data structures implementations of MonadTac might want
module Solver.MonadTacTypes where

import GHC.TypeLits
-- import Solver.MonadTac
import Core
import Text.PrettyPrint.ANSI.Leijen hiding (Pretty (..))
import Control.Concurrent.MVar
import Text.Parsix (Span)
import Frontend.Expr ()

instance Pretty Blame where
  prettyPrec _ (Blame s x) = pretty s <> " " <> pretty x


deriving instance Show (ScopeInfo n)

-- instance Show (ScopeInfo n) where
--   show _ = "<scope>"
instance Pretty (ScopeInfo n) where
  prettyPrec _ (SimpleScope m) = pretty m
  prettyPrec _ (SolverScope _ (ScopeVar v)) = pretty v
  -- prettyPrec _ _ = "<scope>"



deriving instance Show AConstraint

instance Pretty AConstraint where
  -- TODO: that the cod doesn't shift variables here is confusing for reading w/ de bruijn
  -- (one expets an `a -> b` to be a `(_ : a) -> b` & thus in b 0 refers to a, but that isn't true here)
  prettyPrec _ (Unify bl e a b x m) = pretty e <> " ⊢ " <> pretty m <> " = " <> pretty x  <> " : " <> pretty a <> " ~ " <> pretty b <> " (" <> pretty bl <> ")"
  prettyPrec _ (Unify_ bl e a b) = pretty e <> " ⊢ " <> pretty a <> " ~ " <> pretty b <> " (" <> pretty bl <> ")"
  prettyPrec _ (Subtype bl e a b x m) = pretty e <> " ⊢ " <> pretty m <> " = " <> pretty x <> " : " <> pretty a <> " → " <> pretty b <> " (" <> pretty bl <> ")"
  prettyPrec _ (LookupName bl e sc n ty tm) = pretty e <> " ⊢ " <> pretty tm <> " : " <> pretty ty <> " = " <> pretty n <> " in " <> pretty sc <> " (" <> pretty bl <> ")"
  -- prettyPrec _ (DefineName bl e v n ty tm) = pretty e <> " ⊢ " <> pretty n <> " = " <> pretty tm <> " : " <> pretty ty <> " (" <> pretty bl <> ")"
  -- prettyPrec _ (SubtypeTele bl e tv a x b m) = pretty (SnocEnvVar e tv) <> " ⊢ " <> pretty m <> " = " <> pretty x <> " : " <> pretty a <> " →inst-tele " <> pretty b <> " (" <> pretty bl <> ")"
  prettyPrec _ x = text $ show x

newtype ScopeV (n::Nat) = ScopeV Int
  deriving (Show)

instance Pretty (ScopeV n) where
  prettyPrec _ (ScopeV x) = pretty x

-- -- w/ dependent types:
-- -- Nonprincipal : (v : TeleTyVar) -> (ty : Type (e, v)) -> Term (e, v) ty -> InferResult e
-- data InferResult n = Principal (Type n, Term n) | Nonprincipal (TeleTyVar n) (Type (n + 1), Term (n + 1))
--   deriving (Generic)

-- instance Pretty (InferResult n)


