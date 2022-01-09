{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}

module Control.Graded.Trans.Identity where

import Prelude hiding (Monad(..))
import Control.Graded
import Control.Graded.Identity
import Control.Graded.Trans

data IdentityT m (r :: (Sing, k)) a where
  IdentityT :: {runIdentityT :: m f a} -> IdentityT m '(S, f) a

instance (Show (m f a)) => Show (IdentityT m '(S, f) a) where
  show (IdentityT x) = show x

instance Subeffect m f f' => Subeffect (IdentityT m) '(S, f) '(S, f') where
  sub (IdentityT x) = IdentityT (sub x)

instance GFunctor m => GFunctor (IdentityT m) where
  fmapG f (IdentityT x) = IdentityT (fmapG f x)

instance GBindable m f f' => GBindable (IdentityT m) '(S, f) '(S, f') where
  bindG (IdentityT x) k = IdentityT (x >>= (runIdentityT . k))

instance GMonad m => GMonad (IdentityT m :: (Sing, k) -> * -> *) where
  type Unit (IdentityT m) = '(S, Unit m)
  type Seq (IdentityT m) '(S, f) '(S, f') = '(S, Seq m f f')
  type Join (IdentityT m) '(S, f) '(S, f') = '(S, Join m f f')
  return x = IdentityT (return x)

instance GMonadTrans IdentityT where
  type IdG IdentityT = S
  liftG = IdentityT