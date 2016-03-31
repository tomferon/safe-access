{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Control.SafeAccess
  ( ensureAccess
  , Capability(..)
  , Capabilities
  , AccessDecision(..)
  , SafeAccessT(..)
  , MonadSafeAccess(..)
  , liftExceptT
  ) where

import Control.Applicative
import Control.Monad
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Trans.Cont
import Control.Monad.Trans.Identity
import Control.Monad.Trans.List
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.RWS (RWST)
import Control.Monad.Writer

import Data.List

-- | Check that the access is legal or make the monad \"fail\".
ensureAccess :: MonadSafeAccess d m => d -> m ()
ensureAccess descr = do
  caps <- getCapabilities
  let decisions     = map (\cap -> runCapability cap descr) caps
      finalDecision = foldl' mergeDecisions AccessDeniedSoft decisions
  case finalDecision of
    AccessGranted     -> return ()
    _                 -> denyAccess descr

-- | Allow things to be accessed. See 'ensureAccess'.
--
-- @d@ is the type describing an access.
newtype Capability d = MkCapability { runCapability :: d -> AccessDecision }

type Capabilities d = [Capability d]

-- | Control the decision process.
--
-- The constructors are ordered by prevalence. For instance, if two capabilities
-- respectively return 'AccessGranted' and 'AccessDenied',
-- the final decision will be 'AccessDenied'.
data AccessDecision
  = AccessDeniedSoft  -- ^ No but another 'Capability' can still decide to grant
  | AccessGranted     -- ^ Final yes (see explanation)
  | AccessDenied      -- ^ Final no
  deriving (Show, Eq)

mergeDecisions :: AccessDecision -> AccessDecision -> AccessDecision
mergeDecisions a b = case (a, b) of
  (AccessDeniedSoft, _)  -> b
  (_, AccessDeniedSoft)  -> a
  (AccessGranted, _)     -> b
  (_, AccessGranted)     -> a
  _                      -> AccessDenied

-- | A simple monad (transformer) to ensure that data are accessed legitimately.
--
-- The return value is either the description of an access having been denied
-- (left) or the result of the normal computation (right).
newtype SafeAccessT d m a
  = SafeAccessT { runSafeAccessT :: Capabilities d -> m (Either d a) }

instance Monad m => Monad (SafeAccessT d m) where
  return = SafeAccessT . const . return . Right
  ma >>= f = SafeAccessT $ \caps -> do
    ex <- runSafeAccessT ma caps
    case ex of
      Left d  -> return $ Left d
      Right x -> runSafeAccessT (f x) caps

instance MonadTrans (SafeAccessT d) where
  lift = SafeAccessT . const . (Right `liftM`)

instance Functor f => Functor (SafeAccessT d f) where
  fmap f sa = SafeAccessT $ \caps -> fmap (fmap f) $ runSafeAccessT sa caps

instance Applicative f => Applicative (SafeAccessT d f) where
  pure = SafeAccessT . const . pure . Right
  safef <*> safea = SafeAccessT $ \caps ->
    let fef = runSafeAccessT safef caps
        fea = runSafeAccessT safea caps
        ff  = flip fmap fef $ \ef -> case ef of
                Left d  -> const $ Left d
                Right f -> fmap f
    in ff <*> fea

instance MonadIO m => MonadIO (SafeAccessT d m) where
  liftIO = SafeAccessT . const . (Right `liftM`) . liftIO

getCapabilities' :: Monad m => SafeAccessT d m (Capabilities d)
getCapabilities' = SafeAccessT $ return . Right

denyAccess' :: Monad m => d -> SafeAccessT d m ()
denyAccess' = SafeAccessT . const . return . Left

class Monad m => MonadSafeAccess d m where
  getCapabilities :: m (Capabilities d)
  denyAccess      :: d -> m ()

instance Monad m => MonadSafeAccess d (SafeAccessT d m) where
  getCapabilities = getCapabilities'
  denyAccess      = denyAccess'

-- | Lift an action from 'ErrorT' to 'SafeAccessT'.
liftExceptT :: ExceptT d m a -> SafeAccessT d m a
liftExceptT = SafeAccessT . const . runExceptT

instance MonadError e m => MonadError e (SafeAccessT d m) where
  throwError     = lift . throwError
  catchError a h = SafeAccessT $ \caps ->
    catchError (runSafeAccessT a caps) (\e -> runSafeAccessT (h e) caps)

instance MonadReader r m => MonadReader r (SafeAccessT d m) where
  ask       = lift ask
  local f a = SafeAccessT $ local f . runSafeAccessT a

instance MonadState s m => MonadState s (SafeAccessT d m) where
  state = lift . state

instance MonadWriter w m => MonadWriter w (SafeAccessT d m) where
  writer = lift . writer

  listen sma = SafeAccessT $ \caps -> do
    let mea = runSafeAccessT sma caps
    pair <- listen mea
    return $ case pair of
      (Left  d, _) -> Left d
      (Right x, w) -> Right (x, w)

  pass smp = SafeAccessT $ \caps -> do
    let mep = runSafeAccessT smp caps
        mpe = flip liftM mep $ \ep -> case ep of
          Left  d      -> (Left  d, id)
          Right (x, f) -> (Right x, f)
    pass mpe

instance MonadSafeAccess d m => MonadSafeAccess d (ContT e m) where
  getCapabilities = lift getCapabilities
  denyAccess      = lift . denyAccess

instance MonadSafeAccess d m => MonadSafeAccess d (ExceptT e m) where
  getCapabilities = lift getCapabilities
  denyAccess      = lift . denyAccess

instance MonadSafeAccess d m => MonadSafeAccess d (IdentityT m) where
  getCapabilities = lift getCapabilities
  denyAccess      = lift . denyAccess

instance MonadSafeAccess d m => MonadSafeAccess d (ListT m) where
  getCapabilities = lift getCapabilities
  denyAccess      = lift . denyAccess

instance MonadSafeAccess d m => MonadSafeAccess d (MaybeT m) where
  getCapabilities = lift getCapabilities
  denyAccess      = lift . denyAccess

instance MonadSafeAccess d m => MonadSafeAccess d (ReaderT r m) where
  getCapabilities = lift getCapabilities
  denyAccess      = lift . denyAccess

instance (MonadSafeAccess d m, Monoid w)
    => MonadSafeAccess d (RWST r w s m) where
  getCapabilities = lift getCapabilities
  denyAccess      = lift . denyAccess

instance (MonadSafeAccess d m, Monoid w)
    => MonadSafeAccess d (WriterT w m) where
  getCapabilities = lift getCapabilities
  denyAccess      = lift . denyAccess
