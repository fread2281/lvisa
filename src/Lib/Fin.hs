{-# LANGUAGE ScopedTypeVariables, TypeApplications, AllowAmbiguousTypes, UndecidableInstances #-}
-- {-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
module Lib.Fin where


import GHC.TypeLits (CmpNat, KnownNat, Nat)
-- import GHC.TypeLits.Witnesses
import Data.Singletons.Prelude.Num
import Data.Singletons.Prelude.Ord
import Data.Singletons.Prelude.Bool
import Data.Singletons.Prelude.Eq
import Data.Singletons.TypeLits hiding (natVal)
import Data.Singletons

data Fin (n :: Nat) where
  Fin :: forall m n. ((m < n) ~ 'True) => Sing m -> Fin n

assoc :: forall a b c. (a + b) + c :~: a + (b + c)
assoc = unsafeCoerce Refl


finVal :: Fin n -> Int
finVal (Fin p) = fromIntegral $ fromSing p

maxFin :: forall n. Sing n -> Fin (n + 1)
maxFin n = gcastWith prf $ Fin n where
  prf :: CmpNat n (n + 1) :~: 'LT
  prf = unsafeCoerce Refl

finZ :: forall n. Fin (n + 1)
finZ = gcastWith prf $ Fin (SNat @0) where
  prf :: CmpNat 0 (n + 1) :~: 'LT
  prf = unsafeCoerce Refl

finSn :: forall m n. KnownNat m => Fin n -> Fin (n + m)
finSn (Fin (v :: Sing v)) = a @(CmpNat (v + m) (n + m)) @LT $ Fin (v %+ SNat @m)
  where
    a :: forall a b c. (a ~ b => c) -> c
    a = gcastWith (unsafeCoerce Refl :: a :~: b)


finSucc :: forall n. Fin n -> Fin (n + 1)
finSucc (Fin (m@SNat :: Sing m)) = gcastWith prf $
  Fin (m %+ SNat @1)
  where
    prf :: (m < n) ~ a => ((m + 1) < (n + 1)) :~: a
    prf = unsafeCoerce Refl



unsafeFinFromInt :: forall n. Int -> Fin n
unsafeFinFromInt i = reifyNat (fromIntegral i) $
  \(Proxy :: Proxy m) -> gcastWith (unsafeCoerce Refl :: CmpNat m n :~: 'LT) $
    Fin (SNat @m)

instance Eq (Fin n) where
  Fin p == Fin q = fromSing p == fromSing q
instance Ord (Fin n) where
  Fin p `compare` Fin q = fromSing p `compare` fromSing q
instance Hashable (Fin n) where
  hashWithSalt s (Fin n) = hashWithSalt s (fromSing n)
instance Show (Fin n) where
  show (Fin n) = show (fromSing n)

trich :: forall n m r. (KnownNat n, KnownNat m) =>
  (CmpNat n m ~ 'LT => r) ->
  (CmpNat n m ~ 'EQ => r) ->
  (CmpNat n m ~ 'GT => r) -> r
trich lt eq gt = case SNat @n `sCompare` SNat @m of SLT -> lt; SEQ -> eq; SGT -> gt
{-# INLINE trich #-}

-- natCmpZero :: forall m r. KnownNat m => Proxy m -> (CmpNat m 0 ~ 'EQ => r) ->
--               ((CmpNat m 0 ~ 'GT, CmpNat (m - 1) m ~ 'LT, KnownNat (m - 1)) => r) -> r
-- natCmpZero _ a b = trich @m @0 Proxy Proxy
--   (natltzero_absurd (Proxy :: Proxy m))
--   a
--   (gcastWith (unsafeCoerce Refl :: CmpNat (m - 1) m :~: 'LT) $
--    withNatOp (%-) (Proxy :: Proxy m) (Proxy :: Proxy 1) b) where
--   natltzero_absurd :: CmpNat n 0 ~ 'LT => Proxy n -> a
--   natltzero_absurd Proxy = error "absurd: Nat lt zero"

withProxy :: forall a r. Proxy a -> (Proxy a -> r) -> r
withProxy _ r = r (Proxy :: Proxy a)
{-# INLINE withProxy #-}

-- -- finLt :: forall i j. KnownNat j => Fin (i + j) -> ()

-- | Nothing if it is m, Just (x - 1) if it's bigger than m, Just x if it's less than m
finMidElim :: forall n m. KnownNat m => Fin (n + 1 + m) -> Maybe (Fin (n + m))
finMidElim (Fin (v@SNat :: Sing v)) = trich @v @m
  (gcastWith (prf1 (Proxy :: Proxy v) Refl) $ Just (Fin v))
  Nothing
  (gcastWith (prf2 (Proxy :: Proxy v) Refl) $ Just (Fin (v %- SNat @1)))
  where
    prf1 :: Proxy v -> (v < m) :~: True -> (v < (n + m)) :~: True
    prf1 Proxy Refl = unsafeCoerce Refl
    prf2 :: Proxy v -> (v < (n + 1 + m)) :~: True -> ((v - 1) < (n + m)) :~: True
    prf2 Proxy Refl = unsafeCoerce Refl

-- finElim :: forall n. Fin (n + 1) -> Maybe (Fin n)
-- finElim = finMidElim (Proxy :: Proxy 0)

finLt :: forall i j. KnownNat j => Fin (i + j) -> Either (Fin (i + j)) (Fin j)
finLt x@(Fin (SNat :: Sing v)) = trich @v @j (Right $ Fin (SNat @v)) (Left x) (Left x)
  -- (Left (Fin v))
  -- (gcastWith (prf Refl (Left Refl)) $ Right (Fin (Proxy :: Proxy (v - m))))
  -- (gcastWith (prf Refl (Right Refl)) $ Right (Fin (Proxy :: Proxy (v - m))))
  -- where
  --   prf :: CmpNat v (m + o) :~: 'LT ->
  --          Either (CmpNat v m :~: 'EQ) (CmpNat v m :~: 'GT) -> CmpNat (v - m) o :~: 'LT
  --   prf Refl _ = unsafeCoerce Refl


finSplit :: forall m o. KnownNat m => Fin (m + o) -> Either (Fin m) (Fin o)
finSplit (Fin (SNat :: Sing v)) = withKnownNat (SNat @v %- SNat @m) $
  trich @v @m
  (Left (Fin (SNat @v)))
  (gcastWith (prf Refl (Left Refl)) $ Right (Fin (SNat @(v - m))))
  (gcastWith (prf Refl (Right Refl)) $ Right (Fin (SNat @(v - m))))
  where
    prf :: (v < (m + o)) :~: True ->
           Either (CmpNat v m :~: 'EQ) (CmpNat v m :~: 'GT) -> ((v - m) < o) :~: True
    prf Refl _ = unsafeCoerce Refl

finSplit' :: forall m o. KnownNat o => Fin (m + o) -> Either (Fin m) (Fin o)
finSplit' (Fin (SNat :: Sing v)) = withKnownNat (SNat @v %- SNat @o) $
  trich @v @o
  (Right (Fin (SNat @v)))
  (gcastWith (prf Refl (Left Refl)) $ Left (Fin (SNat @(v - o))))
  (gcastWith (prf Refl (Right Refl)) $ Left (Fin (SNat @(v - o))))
  where
    prf :: (v < (m + o)) :~: True ->
           Either (CmpNat v o :~: 'EQ) (CmpNat v o :~: 'GT) -> ((v - o) < m) :~: True
    prf Refl _ = unsafeCoerce Refl


splitFin :: forall i j r. KnownNat j => (Fin i -> r) -> (Fin j -> r) -> Fin (i + j) -> r
splitFin a b x = either a b $ finSplit' x

weakenFin :: forall n m. Fin n -> Fin (m + n)
weakenFin (Fin (v :: Sing v)) = gcastWith (prf @v Refl) $ Fin v where
  prf :: forall v. (v < n) :~: True -> (v < (m + n)) :~: True
  prf Refl = unsafeCoerce Refl

absurdFin :: Fin 0 -> a
absurdFin _ = error "absurdFin"


-- sends (a + k) to (k, Just a) when a < j
finMidAsNat :: forall i j k. (KnownNat j, KnownNat k) => Fin (i + j + k) -> (Fin (i + 1 + k), Maybe (Fin j))
finMidAsNat (Fin (v :: Sing v)) = case v %>= SNat @k of
  STrue ->
    case v %>= (SNat @j %+ SNat @k) of
      STrue -> (a @(CmpNat (v - j + 1) (i + 1 + k)) @LT $
        Fin (v %- SNat @j %+ SNat @1), Nothing)
      SFalse -> (a @(CmpNat k (i + 1 + k)) @LT $ Fin (SNat @k), a @(CmpNat (v - k) j) @LT $ Just (Fin (v %- SNat @k)))
  SFalse -> (a @(CmpNat v (i + 1 + k)) @LT $ Fin v, Nothing)
  where
  a :: forall a b c. (a ~ b => c) -> c
  a = gcastWith (unsafeCoerce Refl :: a :~: b)

-- inverse to finMidAsNat, expects int < j
finNatAsMid :: forall i j k. (KnownNat j, KnownNat k) => Fin (i + 1 + k) -> Either (Fin (i + j + k)) (Fin j -> Fin (i + j + k))
finNatAsMid (Fin (v@SNat :: Sing v)) = case v %>= SNat @k of
  STrue ->
    case v %== SNat @k of
      SFalse -> Left $ a @(CmpNat (v + j - 1) (i + j + k)) @LT $
        Fin (v %+ SNat @j %- SNat @1)
      STrue -> Right $ \(Fin (w :: Sing w)) ->
          a @(CmpNat (v + w) (i + j + k)) @LT $
          Fin (v %+ w)
  SFalse -> Left $ a @(CmpNat v (i + j + k)) @LT $ Fin (SNat @v)
  where
  a :: forall a b c. (a ~ b => c) -> c
  a = gcastWith (unsafeCoerce Refl :: a :~: b)

finMidSplit :: forall i j k. (KnownNat j, KnownNat k) => Fin (i + j + k) -> Maybe (Fin (i + k))
finMidSplit (Fin (v@SNat :: Sing v)) = case v %> SNat @k of
  STrue ->
    case v %> (SNat @j %+ SNat @k) of
      STrue ->
        a @(CmpNat (v - j) (i + k)) @LT $
        Just $ Fin (v %- SNat @j)
      SFalse -> Nothing
  SFalse -> a @(CmpNat v (i + k)) @LT $ Just $ Fin (SNat @v)
  where
    a :: forall a b c. (a ~ b => c) -> c
    a = gcastWith (unsafeCoerce Refl :: a :~: b)
  

-- instance KnownNat k => Enum (Fin k) where
--   toEnum i = reifyNat (fromIntegral i) $ \(_ :: Proxy i) ->
--     case SNat @i %< SNat @k of
--       STrue -> Fin (SNat @i)
--       SFalse -> error "toEnum Fin: too big"
--   fromEnum (Fin s) = fromIntegral $ fromSing s
-- instance (KnownNat k, w ~ (k + 1)) => Bounded (Fin w) where
--   minBound = finZ
--   maxBound = withKnownNat (SNat @k %+ SNat @1) $
--     case SNat @k %< SNat @w of
--       STrue -> Fin (SNat @k)

instance KnownNat k => Finite (Fin k) where
  values = go (SNat @0) (SNat @k) where
    go :: Sing (a :: Nat) -> Sing b -> [Fin b]
    go a b = case a %< b of
      STrue -> Fin a:go (a %+ SNat @1) b
      SFalse -> []

newtype FiniteFun a b = FiniteFun (a -> b)
  deriving (Functor)

-- Bounded, but it can have 0 values too
class Finite a where
  values :: [a]

instance (Finite a, Eq b) => Eq (FiniteFun a b) where
  f == FiniteFun g = getAll $ ifoldMap (\x y -> All $ y == g x) f
instance Finite a => Foldable (FiniteFun a) where
  foldMap g (FiniteFun f) = foldMap (g . f) values
instance Finite a => FoldableWithIndex a (FiniteFun a) where
  ifoldMap g (FiniteFun f) = foldMap (\x -> g x $ f x) values

  
shiftNV :: forall i j k. (KnownNat k, KnownNat j) => Fin (i + k) -> Fin (i + j + k)
shiftNV x = x & finLt @i @k & either f weakenFin
  where
    a :: forall a b x. (a ~ b => x) -> x
    a = gcastWith (unsafeCoerce Refl :: a :~: b)
    
    f :: Fin (i + k) -> Fin (i + j + k)
    f (Fin (v :: Sing v)) = a @(CmpNat (v + j) ((i + j) + k)) @LT $
      Fin (v %+ SNat @j)
  