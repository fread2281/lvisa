module Solver.Pretty where

import Text.PrettyPrint.ANSI.Leijen as P hiding (Pretty(..),(<$>))
import Solver.MonadTacImpl
import Solver.MonadTacTypes
import Core
import Lib.Misc
import Solver.Unify


prettyTy :: Env n -> Type n -> ElabMonad Doc
prettyTy e ty = prettyCore mempty 0 (envNames e) <$> zonk_term (coerce ty)

prettyTm :: Env n -> Term n -> ElabMonad Doc
prettyTm e ty = prettyCore mempty 0 (envNames e) <$> zonk_term (coerce ty)

prettyConstraint :: AConstraint -> ElabMonad Doc
prettyConstraint c = go c where
  -- go (Unify bl e a b m) = pretty e <> " ⊢ " <> pretty m <> " : " <> pretty a <> " ~ " <> pretty b <> " (" <> pretty bl <> ")"
  -- go (Unify_ bl e a b) = pretty e <> " ⊢ " <> pretty a <> " ~ " <> pretty b <> " (" <> pretty bl <> ")"
  -- go (Subtype bl e a b x m) = pretty e <> " ⊢ " <> pretty m <> " = " <> pretty x <> " : " <> pretty a <> " → " <> pretty b <> " (" <> pretty bl <> ")"
  -- go (LookupName bl e sc n ty tm) = pretty e <> " ⊢ " <> pretty tm <> " : " <> pretty ty <> " = " <> pretty n <> " in " <> pretty sc <> " (" <> pretty bl <> ")"
  -- -- go (DefineName bl e v n ty tm) = pretty e <> " ⊢ " <> pretty n <> " = " <> pretty tm <> " : " <> pretty ty <> " (" <> pretty bl <> ")"
  go (Unify bl e a b x m) = do
    a' <- prettyTy e a; b' <- prettyTy e b; x' <- prettyTm e x
    pure $ pretty e <> " ⊢ " <> pretty m <> " = " <> x' <> " : " <> a' <> " ~ " <> b' <> " (" <> pretty bl <> ")"
  go (Subtype bl e a b x m) = do
    x' <- prettyTm e x; a' <- prettyTy e a; b' <- prettyTy e b
    pure $ pretty e <> " ⊢ " <> pretty m <> " = " <> x' <> " : " <> a' <> " → " <> b' <> " (" <> pretty bl <> ")"
  -- go (SubtypeTele bl e tv a x b m) = do
  --   let e' = SnocEnvVar e tv
  --   x' <- prettyTm e' x; a' <- prettyTy e' a; b' <- prettyTy e b
  --   pure $ hang 2 $
  --     "Type inference is stuck: " <$$> 
  --     "term:          " <> x' <$$>
  --     "infered type:  " <> a' <$$>
  --     "expected type: " <> b' <$$>
  --     "resulting meta: " <> pretty m <$$>
  --     "(need more information to figure out if we need to insert an implicit lambda)" <$$>
  --     "environment: " <> pretty (SnocEnvVar e tv) <> " ⊢ " <$$>
  --     "at " <> pretty bl
  go x = pure $ pretty x

prettyMetas :: [Some MetaVar] -> Doc
prettyMetas mvs = fmap (\(Some x) -> f x) mvs & \l -> P.hang 2 ("Referenced metas:" P.<$$> (P.vcat l)) where
  f :: MetaVar n -> Doc
  f mv = pretty mv <> " = " <> pretty (_metaEnv mv) <> " ⊢ " <> x <> " (" <> pretty (_metaSource mv) <> ")" -- <>  (if null blx then "" else " blocked")
      where x = case _metaType mv of IsType -> "type"; HasType ty -> prettyCore mempty 0 ns $ coerce ty
            ns = envNames $ _metaEnv mv

-- instance Pretty MetaInfo where
--   prettyPrec _ (MetaInfo e ty v b blx) = "(" <> pretty e <> " ⊢ " <> x <> maybe "" ((" = " <>) . prettyCore mempty 0 ns . coerce) v <> " (" <> pretty b <> ")" <> ")" <> (if null blx then "" else " blocked")
--     where x = case ty of IsType -> "type"; HasType ty -> prettyCore mempty 0 ns $ coerce ty
--           ns = envNames e
  
prettyState s = do
  cs <- traverse prettyConstraint $ toListOf (constraints.each) s
  pure $
    -- P.hang 2 ("Unsolved metas:" P.<$$> (P.vcat $ fmap pretty $ itoListOf (metaMap .> itraversed . filtered (\(MetaInfo _ _ x _ _) -> isNothing x)) s)) P.<$$>
    P.hang 2 ("Unsolved constraints:" P.<$$> (P.vcat cs)) P.<$$>
    P.hang 2 ("Warnings:" P.<$$> P.vcat (fmap pretty (s ^. warnings)))



