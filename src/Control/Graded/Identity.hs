{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}

module Control.Graded.Identity where

import Control.Graded
import Prelude hiding (Monad(..))
import qualified Prelude as P

data Sing = S

data Identity (r :: Sing) a where
  Identity :: {runIdentity :: a} -> Identity S a

instance Show a => Show (Identity S a) where
  show (Identity x) = show x

instance Subeffect Identity S S where
  sub = id

instance GFunctor Identity where
  fmapG f (Identity x) = Identity (f x)

instance GBindable Identity S S where
  bindG (Identity x) k = k x

instance GMonad (Identity :: Sing -> * -> *) where
  type Unit Identity = S
  type Seq Identity e f = S
  type Join Identity e f = S
  return = Identity