{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module Control.Graded where

import GHC.Exts (Constraint)
import qualified Prelude as P
import Prelude hiding (Monad(..))

class GFunctor (f :: k -> * -> *) where
  fmapG :: (a -> b) -> f r a -> f r b

class GMonad m => GBindable (m :: k -> * -> *) (r :: k) (s :: k) where
  bindG :: m r a -> (a -> m s b) -> m (Seq m r s) b

type LeftId m e = ((Seq m e (Unit m)) ~ e)
type RightId m e = ((Seq m (Unit m) e) ~ e)
type Assoc m e f g = ((Seq m (Seq m e f) g) ~ (Seq m e (Seq m f g)))
type JoinIdemp m e = ((Join m e e) ~ e)
type JoinComm m e f = ((Join m e f) ~ (Join m f e))
type JoinUpper m e f = (Subeffect m e (Join m e f),
                        Subeffect m f (Join m e f))
type Refl m e = Subeffect m e e
type Trans m e f g = (Subeffect m e f, Subeffect m f g, Subeffect m e g)
type Monotonic m e e' f f' = (Subeffect m e e', Subeffect m f f',
                              Subeffect m (Seq m e f) (Seq m e' f'))

class GFunctor m => GMonad (m :: k -> * -> *) where
  type Unit m :: k
  type Seq m (e :: k) (f :: k) :: k
  type Join m (e :: k) (f :: k) :: k
  
  type Inv m (f :: k) (g :: k) :: Constraint
  type Inv m f g = ()
  
  return :: a -> m (Unit m) a

  (>>=) :: GBindable m e f => m e a -> (a -> m f b) -> m (Seq m e f) b
  x >>= k = bindG x k
  (>>) :: GBindable m e f => m e a -> m f b -> m (Seq m e f) b
  x >> y = x >>= const y

  alt :: JoinUpper m e f => Bool -> m e a -> m f a -> m (Join m e f) a
  alt True x y = sub x
  alt False x y = sub y

class Subeffect (m :: k -> * -> *) (e :: k) (f :: k) where
  sub :: m e a -> m f a
