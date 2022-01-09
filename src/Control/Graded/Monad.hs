{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}

module Control.Graded.Monad where

import Control.Graded
import Prelude hiding (Monad(..))
import qualified Prelude as P

data Monad m r a where
  Wrap :: P.Monad m => m a -> Monad m () a

unWrap :: P.Monad m => Monad m r a -> m a
unWrap (Wrap m) = m

instance (P.Monad m, Show (m a)) => Show (Monad m r a) where
  show (Wrap m) = show m

instance (P.Monad m) => Subeffect (Monad m) () () where
  sub = id

instance (P.Monad m) => GFunctor (Monad m) where
  fmapG f (Wrap m) = Wrap (fmap f m)

instance (P.Monad m) => GBindable (Monad m) () () where
  bindG (Wrap x) k = Wrap ((P.>>=) x (unWrap . k))

instance P.Monad m => GMonad (Monad m) where
  type Unit (Monad m) = ()
  type Seq (Monad m) e f = ()
  type Join (Monad m) e f = ()
  return x = Wrap (P.return x)