{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Control.Graded.Trans.PermState where

import Control.Graded
import Control.Graded.PermState
import Control.Graded.Trans
import Prelude hiding (Monad(..))
  
data PermStateT s (m :: k -> * -> *) (f :: (Perm, k)) a where
  PureStateT :: {runPureStateT :: m r a}            -> PermStateT s m '(Pure, r) a
  ROStateT   :: {runROStateT   :: s -> m r a}       -> PermStateT s m '(RO,   r) a
  AWStateT   :: {runAWStateT   :: m r (a, s)}       -> PermStateT s m '(AW,   r) a
  WOStateT   :: {runWOStateT   :: m r (a, Maybe s)} -> PermStateT s m '(WO,   r) a
  RWStateT   :: {runRWStateT   :: s -> m r (a, s)}  -> PermStateT s m '(RW,   r) a

runPermStateT :: GMonad m => PermStateT s m '(p, r) a -> s -> m r (a, s)
runPermStateT (PureStateT m) s = fmapG (\x -> (x, s)) m
runPermStateT (ROStateT f)   s = fmapG (\x -> (x, s)) (f s)
runPermStateT (AWStateT m)   _ = m
runPermStateT (WOStateT m)   s = fmapG (\(x, s') -> case s' of
  Nothing -> (x, s)
  Just y  -> (x, y)) m
runPermStateT (RWStateT f)   s = f s

-- subeffecting
instance Subeffect m f f' => Subeffect (PermStateT s m) '(Pure, f) '(Pure, f') where
  sub (PureStateT m) = PureStateT (sub m)
instance Subeffect m f f' => Subeffect (PermStateT s m) '(AW, f) '(AW, f') where
  sub (AWStateT m) = AWStateT (sub m)
instance Subeffect m f f' => Subeffect (PermStateT s m) '(WO, f) '(WO, f') where
  sub (WOStateT m) = WOStateT (sub m)
instance Subeffect m f f' => Subeffect (PermStateT s m) '(RO, f) '(RO, f') where
  sub (ROStateT f) = ROStateT (\s -> sub (f s))
instance Subeffect m f f' => Subeffect (PermStateT s m) '(RW, f) '(RW, f') where
  sub (RWStateT f) = RWStateT (\s -> sub (f s))
instance Subeffect m f f' => Subeffect (PermStateT s m) '(Pure, f) '(RO, f') where
  sub (PureStateT m) = ROStateT $ const (sub m)
instance (Functor (m f), Subeffect m f f') => Subeffect (PermStateT s m) '(Pure, f) '(WO, f') where
  sub (PureStateT m) = WOStateT $ sub (fmap (\x -> (x, Nothing)) m)
instance (Functor (m f), Subeffect m f f') => Subeffect (PermStateT s m) '(Pure, f) '(RW, f') where
  sub (PureStateT m) = RWStateT $ \s -> sub (fmap (\x -> (x, s)) m)
instance (Functor (m f), Subeffect m f f') => Subeffect (PermStateT s m) '(AW, f) '(WO, f') where
  sub (AWStateT m) = WOStateT $ sub (fmap (\(x, s) -> (x, Just s)) m)
instance (Functor (m f), Subeffect m f f') => Subeffect (PermStateT s m) '(AW, f) '(RW, f') where
  sub (AWStateT m) = RWStateT $ const $ sub (fmap (\(x, s) -> (x, s)) m)
instance (Functor (m f), Subeffect m f f') => Subeffect (PermStateT s m) '(RO, f) '(RW, f') where
  sub (ROStateT f) = RWStateT $ \s -> sub (fmap (\x -> (x, s)) (f s))
instance (Functor (m f), Subeffect m f f') => Subeffect (PermStateT s m) '(WO, f) '(RW, f') where
  sub (WOStateT m)  = RWStateT $ \s' -> sub (fmap (\r -> case r of
    (x, Just s)  -> (x, s)
    (x, Nothing) -> (x, s')) m)

-- binding definition, all the cases
instance GBindable m f f' => GBindable (PermStateT s m) '(Pure, f) '(Pure, f') where
  bindG (PureStateT x) k = PureStateT $ x >>= (runPureStateT . k)
instance GBindable m f f' => GBindable (PermStateT s m) '(Pure, f) '(RO, f') where
  bindG (PureStateT x) k = ROStateT $ \s -> x >>= \r -> runROStateT (k r) s
instance GBindable m f f' => GBindable (PermStateT s m) '(Pure, f) '(AW, f') where
  bindG (PureStateT x) k = AWStateT $ x >>= (runAWStateT . k)
instance GBindable m f f' => GBindable (PermStateT s m) '(Pure, f) '(WO, f') where
  bindG (PureStateT x) k = WOStateT $ x >>= (runWOStateT . k)
instance GBindable m f f' => GBindable (PermStateT s m) '(Pure, f) '(RW, f') where
  bindG (PureStateT x) k = RWStateT $ \s -> (x >>= \r -> runRWStateT (k r) s)

instance GBindable m f f' => GBindable (PermStateT s m) '(RO, f) '(Pure, f') where
  bindG (ROStateT f) k = ROStateT $ \s -> f s >>= (runPureStateT . k)
instance GBindable m f f' => GBindable (PermStateT s m) '(RO, f) '(RO, f') where
  bindG (ROStateT f) k = ROStateT $ \s -> f s >>= \r -> runROStateT (k r) s
instance GBindable m f f' => GBindable (PermStateT s m) '(RO, f) '(AW, f') where
  bindG (ROStateT f) k = RWStateT $ \s -> f s >>= (runAWStateT . k)
instance (GBindable m f f', GBindable m (Seq m f f') (Unit m), LeftId m (Seq m f f')) => GBindable (PermStateT s m) '(RO, f) '(WO, f') where
  bindG (ROStateT f) k = RWStateT $ \s -> f s >>= (runWOStateT . k) >>= \r ->
    let (y, s') = r in case s' of
      Just z  -> return (y, z)
      Nothing -> return (y, s)
instance (GMonad m, GBindable m f f') => GBindable (PermStateT s m) '(RO, f) '(RW, f') where
  bindG (ROStateT f) k = RWStateT $ \s -> f s >>= \r -> runRWStateT (k r) s

instance (GMonad m, GBindable m f f', GBindable m f' (Unit m), LeftId m f') => GBindable (PermStateT s m) '(AW, f) '(Pure, f') where
  bindG (AWStateT m) k = AWStateT $ m >>= \(x, s) -> runPureStateT (k x) >>= \r -> return (r, s)
instance (GMonad m, GBindable m f f', GBindable m f' (Unit m), LeftId m f') => GBindable (PermStateT s m) '(AW, f) '(RO, f') where
  bindG (AWStateT m) k = AWStateT $ m >>= \(x, s) -> runROStateT (k x) s >>= \r -> return (r, s)
instance (GMonad m, GBindable m f f', GBindable m f' (Unit m), LeftId m f') => GBindable (PermStateT s m) '(AW, f) '(AW, f') where
  bindG (AWStateT m) k =  AWStateT $ m >>= \(x, s) -> runAWStateT (k x)
instance (GMonad m, GBindable m f f', GBindable m f' (Unit m), LeftId m f') => GBindable (PermStateT s m) '(AW, f) '(WO, f') where
  bindG (AWStateT m) k =  AWStateT $ m >>= \(x, s) -> runWOStateT (k x) >>= \r ->
    let (y, s') = r in case s' of
      Just z  -> return (y, z)
      Nothing -> return (y, s)
instance (GMonad m, GBindable m f f', LeftId m f') => GBindable (PermStateT s m) '(AW, f) '(RW, f') where
  bindG (AWStateT m) k = AWStateT $ m >>= \(x, s) -> runRWStateT (k x) s

instance (GMonad m, GBindable m f f', GBindable m f' (Unit m), LeftId m f') => GBindable (PermStateT s m) '(WO, f) '(Pure, f') where
  bindG (WOStateT m) k = WOStateT $ m >>= \(x, s) -> runPureStateT (k x) >>= \r -> return (r, s)
instance (GMonad m, GBindable m f f', GBindable m f' (Unit m), LeftId m f') => GBindable (PermStateT s m) '(WO, f) '(RO, f') where
  bindG (WOStateT m) k = RWStateT $ \s -> m >>= \r ->
    let (y, s') = r in case s' of
      Just z  -> runROStateT (k y) z >>= \r' -> return (r', z)
      Nothing -> runROStateT (k y) s >>= \r' -> return (r', s)
instance (GMonad m, GBindable m f f') => GBindable (PermStateT s m) '(WO, f) '(AW, f') where
  bindG (WOStateT m) k = AWStateT $ m >>= \(x, s) -> runAWStateT (k x)
instance (GMonad m, GBindable m f f', GBindable m f' (Unit m), LeftId m f') => GBindable (PermStateT s m) '(WO, f) '(WO, f') where
  bindG (WOStateT m) k = WOStateT $ m >>= \(x, s) -> runWOStateT (k x) >>= \(y, s') ->
    case s' of
      Just z  -> return (y, s')
      Nothing -> return (y, s)
instance (GMonad m, GBindable m f f') => GBindable (PermStateT s m) '(WO, f) '(RW, f') where
  bindG (WOStateT m) k = RWStateT $ \s -> m >>= \(x, s') -> case s' of
    Just y  -> runRWStateT (k x) y
    Nothing -> runRWStateT (k x) s

instance (GMonad m, GBindable m f f', GBindable m f' (Unit m), LeftId m f') => GBindable (PermStateT s m) '(RW, f) '(Pure, f') where
  bindG (RWStateT f) k = RWStateT $ \s -> f s >>= \(y, s') -> runPureStateT (k y) >>= \r -> return (r, s')
instance (GMonad m, GBindable m f f', GBindable m f' (Unit m), LeftId m f') => GBindable (PermStateT s m) '(RW, f) '(RO, f') where
  bindG (RWStateT f) k = RWStateT $ \s -> f s >>= \(y, s') -> runROStateT (k y) s' >>= \r -> return (r, s')
instance (GMonad m, GBindable m f f') => GBindable (PermStateT s m) '(RW, f) '(AW, f') where
  bindG (RWStateT f) k = RWStateT $ \s -> f s >>= \(y, _) -> runAWStateT (k y)
instance (GMonad m, GBindable m f f', GBindable m f' (Unit m), LeftId m f') => GBindable (PermStateT s m) '(RW, f) '(WO, f') where
  bindG (RWStateT f) k = RWStateT $ \s -> f s >>= \(x, s') -> runWOStateT (k x) >>= \(y, s'') -> case s'' of
    Just z  -> return (y, z)
    Nothing -> return (y, s')
instance (GMonad m, GBindable m f f') => GBindable (PermStateT s m) '(RW, f) '(RW, f') where
  bindG (RWStateT f) k = RWStateT $ \s -> f s >>= \(y, s') -> runRWStateT (k y) s'

-- fmapG
instance GFunctor m => GFunctor (PermStateT s m) where
  fmapG f (PureStateT m)  = PureStateT (fmapG f m)
  fmapG f (ROStateT   f') = ROStateT   (\s -> fmapG f (f' s))
  fmapG f (AWStateT   m)  = AWStateT   (fmapG (\(x, s) -> (f x, s)) m)
  fmapG f (WOStateT   m)  = WOStateT   (fmapG (\(x, s) -> (f x, s)) m)
  fmapG f (RWStateT   f') = RWStateT   (\s -> fmapG (\(x, s') -> (f x, s')) (f' s))

instance GMonad m => GMonad (PermStateT s m) where
  type Unit (PermStateT s m) = '(Pure, Unit m)
  type Seq (PermStateT s m) '(e, f) '(e', f') = '(PermSeq e e', Seq m f f')
  type Join (PermStateT s m) '(e, f) '(e', f') = '(PermJoin e e', Join m f f')
  return = PureStateT . return

-- lifting
instance GMonadTrans (PermStateT s) where
  type IdG (PermStateT s) = Pure
  liftG = PureStateT
