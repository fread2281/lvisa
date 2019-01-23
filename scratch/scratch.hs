



-- TODO: this won't work
-- at least the level per thread thing won't without more info about vars
-- consider a var (_,_)
-- at i write (a,_),
-- at j > i write (_,b)
-- need more info about the contents of vars to just backtrack the part from j
-- -- | Run a MVar computation with backtracking that
-- -- explores one tree branch at once, but keeps track for each thread
-- -- how far down the current branch it depends on
-- -- so we can eagerly guess a branch for alts,
-- -- without worrying about hurting sharing
-- --
-- -- does trailing w/ mutability
-- -- 
-- -- TODO: syncronization
-- --
-- -- int is number of alts we're under
-- -- (e.g. tree depth)
-- newtype BacktrackingT m a = BacktrackingT (ReaderT Int m a)
--   deriving (Functor, Applicative, Monad)

-- instance (MVish m, VarM m) => MVish (BacktrackingT m) where
--   type BVar (BacktrackingT m) = Compose (BVar m) ((,) Int)
--   newBVar = 

