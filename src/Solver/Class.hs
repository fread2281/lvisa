{-# LANGUAGE GeneralizedNewtypeDeriving, UndecidableInstances, DefaultSignatures #-}
module Solver.Class where

-- import Control.Monad.ST
-- import Data.STRef
-- import Data.IORef
-- import GHC.Prim
import qualified Control.Concurrent.MVar as MV
import Control.Concurrent (forkIO)
import Control.Monad.Cont
import Solver.Ref
import Control.Monad.Reader
-- import Data.Vector.Mutable
-- import Control.Monad.Primitive
-- import Data.Primitive.MutVar

-- MVar interface w/ fork
class Applicative m => MVish m where
  type MVar m :: * -> *
  newMVar :: m (MVar m a)
  readMVar :: MVar m a -> m a
  -- readMVar' :: MVar m a -> (a -> m b) -> m b -> m b
  tryReadMVar :: MVar m a -> m (Maybe a)
  writeMVar :: MVar m a -> a -> m ()
  fork :: m a -> m ()

  
  default newMVar :: (m ~ t n, MonadTrans t, Monad n, MVish n, MVar n ~ MVar (t n)) => m (MVar m a)
  default readMVar :: (m ~ t n, MonadTrans t, Monad n, MVish n, MVar n ~ MVar (t n)) => MVar m a -> m a
  default tryReadMVar :: (m ~ t n, MonadTrans t, Monad n, MVish n, MVar n ~ MVar (t n)) => MVar m a -> m (Maybe a)
  default writeMVar :: (m ~ t n, MonadTrans t, Monad n, MVish n, MVar n ~ MVar (t n)) => MVar m a -> a -> m ()
  -- default fork :: (m ~ t n, MonadTrans t, Monad n, MVish n, MVar n ~ MVar (t n)) => m a -> m ()
  

  newMVar = lift newMVar
  readMVar = lift . readMVar
  tryReadMVar = lift . tryReadMVar
  writeMVar v x = lift $ writeMVar v x

-- instance (MVish m, Monad m) => MVish (StateT s m) where
--   type MVar (StateT s m) = MVar m


class MVish m => Unblockish m where
  -- TODO: this is insufficient for tele vars 
  readMVar' :: MVar m a -> m a -> m a

-- data MVarContents m a = Empty | Blocked [a -> m ()] [()] | Full a

-- newtype IOV m a = IOV ()

-- newtype IOMVar m a = IOMVar -- (IORef (Maybe a, [a -> m ()], [(a -> m ())]))





instance MVish IO where
  type MVar IO = MV.MVar
  newMVar = MV.newEmptyMVar
  readMVar = MV.readMVar
  tryReadMVar = MV.tryReadMVar
  writeMVar = MV.putMVar
  fork x = forkIO (x >> pure ()) >> pure ()
  -- need fast path/slow path abstraction for e.g. mmatch
  -- could do readMVar' :: MVar m a -> m a -> m a
  -- or something else?
  -- readMVar' :: MVar m a -> (a -> m b) -> m b -> m b?
  -- go w/ first for now



data VarContents m a = Filled a | Blocked [a -> m ()] [(a -> m (), m a)] -- | EmptyV

newtype MVarV m a = MVarV (Ref m (VarContents (MVarT m) a))

deriving instance Eq (Ref m (VarContents (MVarT m) a)) => Eq (MVarV m a)
deriving instance Show (Ref m (VarContents (MVarT m) a)) => Show (MVarV m a)

-- check if it's blocked & run the second action if needed :)
data VarAction m where
  VarAction :: MVar (MVarT m) a -> VarAction m

-- single-threaded mvar emulation, as a transformer on top of a stack w/ IO
-- TODO: is this the right order?
newtype MVarT (m :: * -> *) a = MVarT (ContT () (StateT [VarAction m] m) a)
  deriving (Functor, Applicative, Monad, MonadIO, MonadRef, MonadFail)

instance MonadTrans MVarT where
  lift = MVarT . lift . lift

instance (MonadRef m, Monad m) => MVish (MVarT m) where
  type MVar (MVarT m) = MVarV m
  newMVar = lift $ do
    v <- newRef $ Blocked [] []
    pure $ MVarV v
  tryReadMVar (MVarV v) = lift $ do
    readRef v <&> \case
      Filled x -> Just x
      _ -> Nothing
  writeMVar (MVarV v) x = do
    lift (readRef v) >>= \case
      Filled _ -> lift $ writeRef v $ Filled x
      Blocked xs ys -> do
        lift $ writeRef v $ Filled x
        traverse_ (($ x)) xs
        traverse_ (($ x) . fst) ys
  readMVar (MVarV v) = do
    lift (readRef v) >>= \case
      Filled v -> pure v
      Blocked xs ys -> MVarT $ ContT $ \c -> do
        lift $ writeRef v $ Blocked ((MVarT . lift . c):xs) ys
        pure ()
  -- i think this works? idk
  fork (MVarT (ContT x)) = MVarT $ ContT $ \c -> x (\_ -> pure ()) *> c ()
  -- fork (MVarT (ContT x)) = MVarT $ ContT $ \c -> c () *> x (\_ -> pure ())


instance (MonadRef m, Monad m) => Unblockish (MVarT m) where
  readMVar' (MVarV v) d = do
    lift (readRef v) >>= \case
      Filled v -> pure v
      Blocked xs ys -> MVarT $ ContT $ \c -> do
        lift $ writeRef v $ Blocked xs (((MVarT . lift . c),d):ys)
        pure ()

instance MonadState s m => MonadState s (MVarT m) where
  get = lift get
  put = lift . put


runMVarT :: (Monad m, MonadRef m) => MVarT m a -> (a -> m ()) -> m ()
runMVarT x c = (\(x,[]) -> x) <$> runStateT (runContT (case x <* go of MVarT r -> r) (\a -> lift $ c a)) []
  where go :: (Monad m, MonadRef m) => MVarT m ()
        go = MVarT get >>= \case
          [] -> pure ()
          (VarAction x@(MVarV v):xs) -> MVarT (put xs) >> lift (readRef v) >>= \case
            Filled _ -> go
            Blocked _ (b:_) -> do
              bv <- snd b
              -- TODO: should we still write if b writes?
              writeMVar x bv
              go


