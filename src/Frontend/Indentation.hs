{-# language GeneralizedNewtypeDeriving, BangPatterns, ScopedTypeVariables #-}
-- | Indentation/layout parsing as a monad transformer (for a base parser monad)
--
-- supports heterogeneous indentation (e.g. like '  \t \t   ')
--
-- haskell-style hanging, where nested uses of hanging do nothing, and
-- 
-- haskell-style blocks, where the Worderior of a block need not be indented relative to it's anchor
-- (but we require it indented relative to the parent block)
--
-- the second would be easy to change, first not
{-# LANGUAGE InstanceSigs, ScopedTypeVariables #-}
module Frontend.Indentation where

import Control.Monad.Reader
import Text.Parsix
-- import Text.Parsix.Position
import Data.Char (isSpace)
import qualified Data.Text as T
-- import Data.Bits

-- interface: use hanging & use our continued to parse indentation after newlines
-- (our someSpace in TokenParsing does that for you automatically)

-- word = length list
data IndentType = Unindent | Hanging ![Text] !Word | Block ![Text] !Word

data IndentState = Indents !Word | DoneWithLine

-- text is current indentation format (at parent if hanging, or at start of block if block)
-- Word is current number of indentation levels, <= length text,
-- bool is if we're hanging & on the same line as the anchor
newtype IndentT m a = IndentT { unIndentT :: ReaderT IndentType (StateT IndentState m) a }
  -- TODO: parser's mtl instances have an unneeded MonadPlus, maybe fix that
  deriving (Functor, Applicative, Monad, Alternative, MonadPlus, Parsing, SliceParsing)
instance MonadTrans IndentT where
  lift = IndentT . lift . lift
instance (TokenParsing m, MonadPlus m) => TokenParsing (IndentT m) where
  someSpace = (do
    _ <- many (char ' ')
    _ <- optional (char '\n' *> continued)
    pure ()) <?> "whitespace"
-- everything that might consume input uses CharParsing (or TokenParsing)
-- and it's sufficient to check when we might consume input
instance (CharParsing m, MonadPlus m) => CharParsing (IndentT m) where
  satisfy f = check *> lift (satisfy f)

runIndentT :: Functor m => IndentT m a -> m a
runIndentT (IndentT x) = fst <$> runStateT (runReaderT x (Block [] 0)) (Indents 0)

-- | Parses indentation and updates the current indentation (/relation to the current parent indentation format)
--
-- use this after newlines & then use check under an alt (e.g. (check *> a) <|> pure b)
continued :: forall m. CharParsing m => IndentT m ()
continued = coerce $ \(t :: IndentType) (_ :: IndentState) -> go 0 (s t)
  where
  go :: Word -> [Text] -> m ((),IndentState)
  go !i [] = (some (char ' ') *> pure ((),Indents (i + 1))) <|> pure ((),Indents i)
  go !i (x:xs) = (text x *> go (i + 1) xs) <|> pure ((),Indents i)

  s :: IndentType -> [Text]
  s Unindent = []
  s (Hanging t _) = t
  s (Block t _) = t

check :: forall m. Parsing m => IndentT m ()
check = coerce $ \f t -> case t of
  DoneWithLine -> pure ((),t)
  Indents s -> case f of
    Unindent -> (pure ((),t) :: m _)
    -- TODO: could set t = DoneWithLine here as an optimization
    Hanging _ x -> if s > x then pure ((),t) else (,t) <$> unexpected "wrong indentation"
    Block _ x -> if s == x then pure ((),t) else (,t) <$> unexpected "wrong indentation"

-- it's important not to consume a newline before calling hanging, 
-- and CharParsing for IndentT automatically consumes newlines,
-- so here's a convenience function
hangingAnchor :: forall m a b. (MonadPlus m, Parsing m, TokenParsing m) => m b -> IndentT m a -> IndentT m a
hangingAnchor a f = lift a *> hanging (someSpace *> f)

-- beware!: it's important not to consume a newline before calling hanging, 
-- and CharParsing for IndentT automatically consumes newlines,
-- so you need to either use lift yourself or use hangingAnchor
hanging :: forall m a. (Monad m, Parsing m) => IndentT m a -> IndentT m a
-- we can get away with just using our parent's indent format (block will update it when it's actually needed)
-- (we don't need to figure out the actual indentation of the start of the current line here, since that isn't actually the rule,
-- indentation only needs to be GT the parent block)
hanging (IndentT f) = IndentT $ ask >>= \fmt -> case fmt of
  Block y x -> put DoneWithLine *> local (\_ -> Hanging y x) f
  Hanging y x -> f
  -- _ -> f

unindent :: (Monad m, Parsing m) => IndentT m a -> IndentT m a
unindent (IndentT f) = check *> IndentT (local (\_ -> Unindent) f <* put DoneWithLine)

-- hanging x = coerce $ \(t :: [Text]) !(i :: Word) -> (coerce x (clearBit i 63) t (setBit i 63) :: m (a, Word))

-- newtype BlockT m a = BlockT (ReaderT Word (IndentT m) a)
--   deriving (Functor, Applicative, Monad, Alternative, SliceParsing, Parsing)

-- TODO: automatic newline consumption is confusig w/ block
-- so should have some way to avoid that
block :: forall m a. (SliceParsing m, CharParsing m, TokenParsing m, MonadPlus m) => IndentT m a -> IndentT m a
block (IndentT b) = IndentT $
  skipMany (satisfy (\x -> isSpace x && x /= '\n' && x /= '\r')) *>
  ((<|>)
    ((string "\n" <|> string "\r\n") *> (unIndentT continued' >>= (\t -> local (\_ -> t) b)))
    -- TODO: need to add case for no newline &
    -- compute how many spaces to expect in case of no newline, e.g.:
    -- do a
    --    b
    -- position >>= \p -> let
    --   -- TODO: next uses tabstop = 8 (that doesn't matter here since we're just recomputing the computed positions, but will probably hurt error locs)
    --   l = visualColumn $ foldr (\c -> next c 0) (Position 0 0 0) $ concat $ fmap T.unpack t
    --   n = visualColumn p - l
    --   in (coerce b t EQ :: m (a, Ordering))
    empty)
 where
  c :: IndentType -> Maybe ([Text],Word)
  c Unindent = Nothing
  c (Hanging f i) = Just (f, i)
  c (Block f i) = Just (f, i)

  continued' :: (CharParsing m, TokenParsing m) => IndentT m IndentType
  continued' = IndentT $ ask >>= \t -> case c t of
    Nothing -> ((\i -> Block [i] 1) . T.pack <$> many (char ' ')) <* put (Indents 1)
    Just (f,i) -> ((\f' -> Block (f ++ [f']) (i + 1)) <$> (lift . lift) (go i f)) <* put (Indents (i + 1))
    where
      go :: Word -> [Text] -> m Text
      go !i [] = T.pack <$> some (char ' ')
      go !i (x:xs) = text x *> go (i+1) xs

