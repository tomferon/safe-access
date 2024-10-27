{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TupleSections #-}

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
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.RWS (RWST(..))
import Control.Monad.Writer
import Data.Bifunctor

-- | Allow things to be accessed. See 'ensureAccess'.
--
-- @d@ is the type describing an access.
newtype Capability m d b
  = MkCapability { runCapability :: d -> m (AccessDecision b) }

instance Applicative m => Semigroup (Capability m d b) where
  (<>) cap1 cap2 = MkCapability $ \d ->
    (<>) <$> runCapability cap1 d <*> runCapability cap2 d

instance Applicative m => Monoid (Capability m d b) where
  mempty = MkCapability $ \_ -> pure mempty
  mappend = (<>)

type Capabilities m d b = [Capability m d b]

-- | Create a capability which only allows a given access
singleCapability :: (Applicative f, Eq d) => d -> Capability f d b
singleCapability = someCapabilities . pure

-- | Create a capability which only allows given accesses
someCapabilities :: (Applicative f, Eq d) => [d] -> Capability f d b
someCapabilities ds = MkCapability $ \d ->
  pure $ if d `elem` ds then AccessGranted else mempty

-- | A special capability which allows every access. Be careful with this!
passthroughCapability :: Applicative f => Capability f d b
passthroughCapability = MkCapability $ \_ -> pure AccessGranted

-- | Control the decision process.
--
-- The constructors are ordered by prevalence. For instance, if two capabilities
-- respectively return 'AccessGranted' and 'AccessDenied', the final decision
-- will be 'AccessDenied'.
--
-- When denying access, additional information can be passed along.
data AccessDecision b
  = AccessDeniedSoft [b] -- ^ No but another 'Capability' can still decide to grant
  | AccessGranted        -- ^ Final yes (see explanation)
  | AccessDenied     [b] -- ^ Final no
  deriving (Show, Eq)

instance Semigroup (AccessDecision b) where
  a <> b = case (a, b) of
    (AccessGranted, AccessDenied _) -> b
    (AccessGranted, _) -> AccessGranted

    (AccessDenied xs, AccessDenied ys) -> AccessDenied (xs ++ ys)
    (AccessDenied _, _) -> a

    (AccessDeniedSoft _, AccessGranted) -> AccessGranted
    (AccessDeniedSoft _, AccessDenied _) -> b
    (AccessDeniedSoft xs, AccessDeniedSoft ys) -> AccessDeniedSoft (xs ++ ys)

instance Monoid (AccessDecision b) where
  mempty = AccessDeniedSoft []
  mappend = (<>)

-- | A simple monad transformer to ensure that data are accessed legitimately.
--
-- The return value is either the description of an access having been denied
-- (left) or the result of the normal computation (right).
newtype SafeAccessT d b m a
  = SafeAccessT { runSafeAccessT :: Capabilities m d b -> m (Either (d, [b]) a) }

instance Functor f => Functor (SafeAccessT d b f) where
  fmap f sa = SafeAccessT $ \caps -> fmap (fmap f) $ runSafeAccessT sa caps

instance Applicative f => Applicative (SafeAccessT d b f) where
  pure = SafeAccessT . const . pure . Right
  safef <*> safea = SafeAccessT $ \caps ->
    let fef = runSafeAccessT safef caps
        fea = runSafeAccessT safea caps
        ff  = flip fmap fef $ \ef -> case ef of
                Left err -> const $ Left err
                Right f  -> fmap f
    in ff <*> fea

instance Monad m => Monad (SafeAccessT d b m) where
  ma >>= f = SafeAccessT $ \caps -> do
    ex <- runSafeAccessT ma caps
    case ex of
      Left err -> return $ Left err
      Right x  -> runSafeAccessT (f x) caps

instance MonadTrans (SafeAccessT d b) where
  lift = SafeAccessT . const . (Right `liftM`)

instance MonadIO m => MonadIO (SafeAccessT d b m) where
  liftIO = SafeAccessT . const . (Right `liftM`) . liftIO

-- | Check that the access is legal or make the monad \"fail\".
ensureAccess :: MonadSafeAccess d b m s => d -> m ()
ensureAccess descr = do
  caps      <- getCapabilities
  decisions <- liftSub $ mapM (\cap -> runCapability cap descr) caps
  case mconcat decisions of
    AccessGranted       -> return ()
    AccessDenied xs     -> denyAccess descr xs
    AccessDeniedSoft xs -> denyAccess descr xs

-- | Allow certain accesses regardless of the capabilities. (unsecure!)
unsecureAllow :: (Monad m, Eq d) => [d] -> SafeAccessT d b m a
              -> SafeAccessT d b m a
unsecureAllow descrs action = do
  caps <- getCapabilities
  let cap = MkCapability $ \descr ->
        if descr `elem` descrs
          then pure AccessGranted
          else mconcat <$> sequenceA (map (flip runCapability descr) caps)
  SafeAccessT $ \_ -> runSafeAccessT action [cap]

getCapabilities' :: Monad m => SafeAccessT d b m (Capabilities m d b)
getCapabilities' = SafeAccessT $ return . Right

denyAccess' :: Monad m => d -> [b] -> SafeAccessT d b m ()
denyAccess' = curry $ SafeAccessT . const . return . Left

catchAccessError'
  :: Monad m
  => SafeAccessT d b m a
  -> (d -> [b] -> SafeAccessT d b m a)
  -> SafeAccessT d b m a
catchAccessError' action handler = SafeAccessT $ \caps -> do
  eRes <- runSafeAccessT action caps
  case eRes of
    Left  (descr, xs) -> runSafeAccessT (handler descr xs) caps
    Right _ -> return eRes

class (Monad m, Monad s) => MonadSafeAccess d b m s | m -> s, m -> d, m -> b where
  getCapabilities  :: m (Capabilities s d b)
  liftSub          :: s a -> m a
  denyAccess       :: d -> [b] -> m ()

  -- | Catch an access error, i.e. an access descriptor which resulted into an
  -- access denied given the capabilities.
  catchAccessError :: m a -> (d -> [b] -> m a) -> m a

instance Monad m => MonadSafeAccess d b (SafeAccessT d b m) m where
  getCapabilities  = getCapabilities'
  liftSub          = lift
  denyAccess       = denyAccess'
  catchAccessError = catchAccessError'

-- | Lift an action from 'ErrorT' to 'SafeAccessT'.
liftExceptT :: Functor m => ExceptT d m a -> SafeAccessT d b m a
liftExceptT action = SafeAccessT $ \_ ->
  fmap (first (,[])) . runExceptT $ action

instance MonadError e m => MonadError e (SafeAccessT d b m) where
  throwError     = lift . throwError
  catchError a h = SafeAccessT $ \caps ->
    catchError (runSafeAccessT a caps) (\e -> runSafeAccessT (h e) caps)

instance MonadReader r m => MonadReader r (SafeAccessT d b m) where
  ask       = lift ask
  local f a = SafeAccessT $ local f . runSafeAccessT a

instance MonadState s m => MonadState s (SafeAccessT d b m) where
  state = lift . state

instance MonadWriter w m => MonadWriter w (SafeAccessT d b m) where
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
               => Capability m d b -> Capability (t m) d b
liftCapability cap = MkCapability $ \descr -> lift $ runCapability cap descr

instance MonadSafeAccess d b m s => MonadSafeAccess d b (ContT e m) s where
  getCapabilities = lift getCapabilities
  liftSub         = lift . liftSub
  denyAccess d xs = lift $ denyAccess d xs
  catchAccessError action handler = ContT $ \cont ->
    catchAccessError (runContT action cont)
                     (\descr xs -> runContT (handler descr xs) cont)

instance MonadSafeAccess d b m s => MonadSafeAccess d b (ExceptT e m) s where
  getCapabilities = lift getCapabilities
  liftSub         = lift . liftSub
  denyAccess d xs = lift $ denyAccess d xs
  catchAccessError action handler = ExceptT $
    catchAccessError
      (runExceptT action)
      (\descr xs -> runExceptT (handler descr xs))

instance MonadSafeAccess d b m s => MonadSafeAccess d b (StateT s' m) s where
  getCapabilities = lift getCapabilities
  liftSub         = lift . liftSub
  denyAccess d xs = lift $ denyAccess d xs
  catchAccessError action handler = StateT $ \s ->
    catchAccessError (runStateT action s)
                     (\descr xs -> runStateT (handler descr xs) s)

instance MonadSafeAccess d b m s => MonadSafeAccess d b (IdentityT m) s where
  getCapabilities = lift getCapabilities
  liftSub         = lift . liftSub
  denyAccess d xs = lift $ denyAccess d xs
  catchAccessError action handler = IdentityT $
    catchAccessError
      (runIdentityT action)
      (\descr xs -> runIdentityT (handler descr xs))

instance MonadSafeAccess d b m s => MonadSafeAccess d b (MaybeT m) s where
  getCapabilities = lift getCapabilities
  liftSub         = lift . liftSub
  denyAccess d xs = lift $ denyAccess d xs
  catchAccessError action handler = MaybeT $
    catchAccessError
      (runMaybeT action)
      (\descr xs -> runMaybeT (handler descr xs))

instance MonadSafeAccess d b m s => MonadSafeAccess d b (ReaderT r m) s where
  getCapabilities = lift getCapabilities
  liftSub         = lift . liftSub
  denyAccess d xs = lift $ denyAccess d xs
  catchAccessError action handler = ReaderT $ \r ->
    catchAccessError (runReaderT action r)
                     (\descr xs -> runReaderT (handler descr xs) r)

instance (MonadSafeAccess d b m s, Monoid w)
    => MonadSafeAccess d b (RWST r w st m) s where
  getCapabilities = lift getCapabilities
  liftSub         = lift . liftSub
  denyAccess d xs = lift $ denyAccess d xs
  catchAccessError action handler = RWST $ \r s ->
    catchAccessError (runRWST action r s)
                     (\descr xs -> runRWST (handler descr xs) r s)

instance (MonadSafeAccess d b m s, Monoid w)
    => MonadSafeAccess d b (WriterT w m) s where
  getCapabilities = lift getCapabilities
  liftSub         = lift . liftSub
  denyAccess d xs = lift $ denyAccess d xs
  catchAccessError action handler = WriterT $
    catchAccessError
      (runWriterT action)
      (\descr xs -> runWriterT (handler descr xs))
