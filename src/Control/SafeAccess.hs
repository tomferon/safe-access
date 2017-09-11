{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FunctionalDependencies #-}

module Control.SafeAccess
  ( Capability(..)
  , Capabilities
  , AccessDecision(..)
  , SafeAccessT(..)
  , MonadSafeAccess(..)
  , ensureAccess
  , unsecureAllow
  , singleCapability
  , someCapabilities
  , passthroughCapability
  , liftExceptT
  , liftCapability
  ) where

import Control.Monad
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Trans.Cont (ContT(..))
import Control.Monad.Trans.Identity
import Control.Monad.Trans.List
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.RWS (RWST(..))
import Control.Monad.Writer

-- | Allow things to be accessed. See 'ensureAccess'.
--
-- @d@ is the type describing an access.
newtype Capability m d = MkCapability { runCapability :: d -> m AccessDecision }

instance Applicative m => Monoid (Capability m d) where
  mempty = MkCapability $ \_ -> pure mempty
  mappend cap1 cap2 = MkCapability $ \d ->
    mappend <$> runCapability cap1 d <*> runCapability cap2 d

type Capabilities m d = [Capability m d]

-- | Create a capability which only allows a given access
singleCapability :: (Applicative f, Eq d) => d -> Capability f d
singleCapability = someCapabilities . pure

-- | Create a capability which only allows given accesses
someCapabilities :: (Applicative f, Eq d) => [d] -> Capability f d
someCapabilities ds = MkCapability $ \d ->
  pure $ if d `elem` ds then AccessGranted else AccessDeniedSoft

-- | A special capability which allows every access. Be careful with this!
passthroughCapability :: Applicative f => Capability f d
passthroughCapability = MkCapability $ \_ -> pure AccessGranted

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

instance Monoid AccessDecision where
  mempty      = AccessDeniedSoft
  mappend a b = case (a, b) of
    (AccessDeniedSoft, _)          -> b
    (_, AccessDeniedSoft)          -> a
    (AccessDenied, _)              -> AccessDenied
    (_, AccessDenied)              -> AccessDenied
    (AccessGranted, AccessGranted) -> AccessGranted

-- | A simple monad transformer to ensure that data are accessed legitimately.
--
-- The return value is either the description of an access having been denied
-- (left) or the result of the normal computation (right).
newtype SafeAccessT d m a
  = SafeAccessT { runSafeAccessT :: Capabilities m d -> m (Either d a) }

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

instance Monad m => Monad (SafeAccessT d m) where
  return = SafeAccessT . const . return . Right
  ma >>= f = SafeAccessT $ \caps -> do
    ex <- runSafeAccessT ma caps
    case ex of
      Left d  -> return $ Left d
      Right x -> runSafeAccessT (f x) caps

instance MonadTrans (SafeAccessT d) where
  lift = SafeAccessT . const . (Right `liftM`)

instance MonadIO m => MonadIO (SafeAccessT d m) where
  liftIO = SafeAccessT . const . (Right `liftM`) . liftIO

-- | Check that the access is legal or make the monad \"fail\".
ensureAccess :: MonadSafeAccess d m s => d -> m ()
ensureAccess descr = do
  caps      <- getCapabilities
  decisions <- liftSub $ mapM (\cap -> runCapability cap descr) caps
  case mconcat decisions of
    AccessGranted -> return ()
    _             -> denyAccess descr

-- | Allow certain accesses regardless of the capabilities. (unsecure!)
unsecureAllow :: (Monad m, Eq d) => [d] -> SafeAccessT d m a
              -> SafeAccessT d m a
unsecureAllow descrs action = do
  caps <- getCapabilities
  let cap = MkCapability $ \descr ->
        if descr `elem` descrs
          then pure AccessGranted
          else mconcat <$> sequenceA (map (flip runCapability descr) caps)
  SafeAccessT $ \_ -> runSafeAccessT action [cap]

getCapabilities' :: Monad m => SafeAccessT d m (Capabilities m d)
getCapabilities' = SafeAccessT $ return . Right

denyAccess' :: Monad m => d -> SafeAccessT d m ()
denyAccess' = SafeAccessT . const . return . Left

catchAccessError' :: Monad m => SafeAccessT d m a -> (d -> SafeAccessT d m a)
                  -> SafeAccessT d m a
catchAccessError' action handler = SafeAccessT $ \caps -> do
  eRes <- runSafeAccessT action caps
  case eRes of
    Left  descr -> runSafeAccessT (handler descr) caps
    Right _     -> return eRes

class (Monad m, Monad s) => MonadSafeAccess d m s | m -> s, m -> d where
  getCapabilities  :: m (Capabilities s d)
  liftSub          :: s a -> m a
  denyAccess       :: d -> m ()

  -- | Catch an access error, i.e. an access descriptor which resulted into an
  -- access denied given the capabilities.
  catchAccessError :: m a -> (d -> m a) -> m a

instance Monad m => MonadSafeAccess d (SafeAccessT d m) m where
  getCapabilities  = getCapabilities'
  liftSub          = lift
  denyAccess       = denyAccess'
  catchAccessError = catchAccessError'

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

liftCapability :: (Monad m, MonadTrans t)
               => Capability m d -> Capability (t m) d
liftCapability cap = MkCapability $ \descr -> lift $ runCapability cap descr

instance MonadSafeAccess d m s => MonadSafeAccess d (ContT e m) s where
  getCapabilities = lift getCapabilities
  liftSub         = lift . liftSub
  denyAccess      = lift . denyAccess
  catchAccessError action handler = ContT $ \cont ->
    catchAccessError (runContT action cont)
                     (\descr -> runContT (handler descr) cont)

instance MonadSafeAccess d m s => MonadSafeAccess d (ExceptT e m) s where
  getCapabilities = lift getCapabilities
  liftSub         = lift . liftSub
  denyAccess      = lift . denyAccess
  catchAccessError action handler = ExceptT $
    catchAccessError (runExceptT action) (runExceptT . handler)

instance MonadSafeAccess d m s => MonadSafeAccess d (IdentityT m) s where
  getCapabilities = lift getCapabilities
  liftSub         = lift . liftSub
  denyAccess      = lift . denyAccess
  catchAccessError action handler = IdentityT $
    catchAccessError (runIdentityT action) (runIdentityT . handler)

instance MonadSafeAccess d m s => MonadSafeAccess d (ListT m) s where
  getCapabilities = lift getCapabilities
  liftSub         = lift . liftSub
  denyAccess      = lift . denyAccess
  catchAccessError action handler = ListT $
    catchAccessError (runListT action) (runListT . handler)

instance MonadSafeAccess d m s => MonadSafeAccess d (MaybeT m) s where
  getCapabilities = lift getCapabilities
  liftSub         = lift . liftSub
  denyAccess      = lift . denyAccess
  catchAccessError action handler = MaybeT $
    catchAccessError (runMaybeT action) (runMaybeT . handler)

instance MonadSafeAccess d m s => MonadSafeAccess d (ReaderT r m) s where
  getCapabilities = lift getCapabilities
  liftSub         = lift . liftSub
  denyAccess      = lift . denyAccess
  catchAccessError action handler = ReaderT $ \r ->
    catchAccessError (runReaderT action r)
                     (\descr -> runReaderT (handler descr) r)

instance (MonadSafeAccess d m s, Monoid w)
    => MonadSafeAccess d (RWST r w st m) s where
  getCapabilities = lift getCapabilities
  liftSub         = lift . liftSub
  denyAccess      = lift . denyAccess
  catchAccessError action handler = RWST $ \r s ->
    catchAccessError (runRWST action r s)
                     (\descr -> runRWST (handler descr) r s)

instance (MonadSafeAccess d m s, Monoid w)
    => MonadSafeAccess d (WriterT w m) s where
  getCapabilities = lift getCapabilities
  liftSub         = lift . liftSub
  denyAccess      = lift . denyAccess
  catchAccessError action handler = WriterT $
    catchAccessError (runWriterT action) (runWriterT . handler)
