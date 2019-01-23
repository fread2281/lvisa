{-# LANGUAGE RoleAnnotations, GeneralizedNewtypeDeriving #-}
-- copy/paste of vault package, needed because
-- vault doesn't have an `instance Eq (Key a)`
module Solver.Vault where

import Prelude hiding (Any)
-- This implementation is specific to GHC
-- und uses  unsafeCoerce  for reasons of efficiency.
import GHC.Exts (Any)
import Unsafe.Coerce (unsafeCoerce)
import Data.Unique.Really
import qualified Data.HashMap.Lazy as Map
import Data.Functor.Classes

toAny :: a -> Any
toAny = unsafeCoerce

fromAny :: Any -> a
fromAny = unsafeCoerce

{-----------------------------------------------------------------------------
    Vault
------------------------------------------------------------------------------}
newtype Vault = Vault (Map.HashMap Unique Any)
newtype Key a = Key Unique
  deriving (Eq, Hashable)

instance Eq1 Key where
  liftEq f (Key a) (Key b) = a == b

type role Key nominal

newKey = Key <$> newUnique

lookup (Key k) (Vault m) = fromAny <$> Map.lookup k m

insert (Key k) x (Vault m) = Vault $ Map.insert k (toAny x) m

adjust f (Key k) (Vault m) = Vault $ Map.adjust f' k m
    where f' = toAny . f . fromAny

delete (Key k) (Vault m) = Vault $ Map.delete k m

{-----------------------------------------------------------------------------
    Locker
------------------------------------------------------------------------------}
data Locker s = Locker !Unique !Any

lock (Key k) = Locker k . toAny

unlock (Key k) (Locker k' a)
  | k == k' = Just $ fromAny a
  | otherwise = Nothing

