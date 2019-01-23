{-# LANGUAGE ScopedTypeVariables #-}
module Lib.Misc where

import qualified Data.HashMap.Lazy as M
-- import Control.Concurrent.Supply
import Data.Constraint.Forall

-- hashmap w/ the correct Monoid instance (unionWith (<>))
newtype MHashMap k a = MHashMap (HashMap k a)

instance (Eq k, Hashable k, Semigroup a) => Semigroup (MHashMap k a) where
  MHashMap x <> MHashMap y = MHashMap $ M.unionWith (<>) x y
instance (Eq k, Hashable k, Semigroup a) => Monoid (MHashMap k a) where
  mappend = (<>)
  mempty = MHashMap M.empty
type instance Index (MHashMap k a) = k
type instance IxValue (MHashMap k a) = a
instance (Eq k, Hashable k) => Ixed (MHashMap k a) where
instance (Eq k, Hashable k) => At (MHashMap k a) where
  at k l (MHashMap v) = MHashMap <$> at k l v


data Some (f :: k -> *) where
  Some :: f x -> Some f

instance forall f. (ForallF Pretty f) => Pretty (Some f) where
  prettyPrec p (Some (x :: f x)) = prettyPrec p x \\ instF @Pretty @f @x

-- instance Pretty Supply where
--   prettyPrec _ _ = mempty
instance Pretty (f (g x)) => Pretty (Compose f g x) where
  prettyPrec p (Compose x) = prettyPrec p x


-- free category
newtype Cat c a b = Cat { lowerCat :: forall r. Category r => (forall x y. c x y -> r x y) -> r a b }

instance Category (Cat c) where
  id = Cat $ \_ -> id
  Cat f . Cat g = Cat (\r -> f r . g r)
-- instance (forall x y. Eq (c x y)) => Eq (Cat c a b) where
--   Cat f == Cat g = _

liftCat :: c a b -> Cat c a b
liftCat x = Cat $ \r -> r x

-- opposite category
newtype Op c a b = Op { runOp :: c b a }

instance Category c => Category (Op c) where
  id = Op id
  Op f . Op g = Op (g . f)
