{-# LANGUAGE GeneralizedNewtypeDeriving, UndecidableInstances, DefaultSignatures #-}
module Solver.Ref where

-- import Control.Monad.State
import Data.Primitive.MutVar
import Control.Monad.Primitive
import qualified Solver.Vault as V
import Control.Monad.Cont


-- typeclasses for IORef, STRef, vault,
-- & e.g. backtracking versions of them
class MonadRef m where
  type Ref m :: * -> *
  newRef :: a -> m (Ref m a)
  writeRef :: Ref m a -> a -> m ()
  readRef :: Ref m a -> m a
  default newRef :: (m ~ t n, MonadTrans t, Monad n, Ref m ~ Ref n, MonadRef n) => a -> m (Ref m a)
  newRef = lift . newRef
  default writeRef :: (m ~ t n, MonadTrans t, Monad n, Ref m ~ Ref n, MonadRef n) => Ref m a -> a -> m ()
  writeRef r x = lift (writeRef r x)
  default readRef :: (m ~ t n, MonadTrans t, Monad n, Ref m ~ Ref n, MonadRef n) => Ref m a -> m a
  readRef = lift . readRef

instance MonadRef IO where
  type Ref IO = MutVar (PrimState IO)
  newRef = newMutVar
  writeRef = writeMutVar
  readRef = readMutVar


instance (MonadRef m, Monad m) => MonadRef (ContT r m) where
  type Ref (ContT r m) = Ref m
instance (MonadRef m, Monad m) => MonadRef (StateT s m) where
  type Ref (StateT s m) = Ref m


-- newtype Key s a = Key (MutVar s (Proxy a))
--   deriving (Eq)

-- newKey :: PrimMonad m => m (Key (PrimState m) a)
-- newKey = Key <$> newMutVar Proxy
 
-- instance TestEquality (Key s) where
--   testEquality x y
--     | x == coerce y = Just $ unsafeCoerce Refl
--     | otherwise = Nothing

-- an implementation of MonadRef using a hashmap
-- for easy backtrackin
newtype VaultT m a = VaultT { unVaultT :: StateT V.Vault m a }
  deriving (Functor, Applicative, Monad, MonadIO, MonadFail)

runVaultT (VaultT v) = runStateT v (V.Vault mempty)


instance MonadIO m => MonadRef (VaultT m) where
  type Ref (VaultT m) = V.Key
  newRef x = do
    k <- liftIO V.newKey
    VaultT $ modify (V.insert k x)
    pure k
  writeRef k v = VaultT $ modify (V.insert k v)
  readRef k = maybe (error "MonadRef Vault: lookup of key not in map (invariant violated)") id . V.lookup k <$> VaultT get




-- -- modifyRef :: Ref m a -> (a -> m a) -> m ()
-- -- modifyRef 

-- data TrailElem m where
--   TrailElem :: Ref m a -> a -> TrailElem m

-- newtype BacktrackingT m a = BacktrackingT (ReaderT (Ref m [[TrailElem m]],Int) m a)
--   deriving (Functor, Applicative, Monad)

-- instance (RefM m, Monad m) => RefM (BacktrackingT m) where
--   type Ref (BacktrackingT m) = Compose (Ref m) ((,) Int)
--   newRef x = BacktrackingT $ ask >>= \(_,l) -> Compose <$> lift (newRef (l,x))
--   readRef (Compose x) = BacktrackingT $ snd <$> lift (readRef x)
--   writeRef (Compose v) x = BacktrackingT $ ask >>= \(t,i) -> do
--     _




