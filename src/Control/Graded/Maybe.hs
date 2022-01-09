{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}

module Control.Graded.Maybe where

import Control.Graded

data MaybeGr = T | F | U

type family MaybeMult r s where
  MaybeMult F _ = F
  MaybeMult T s = s
  MaybeMult U F = F
  MaybeMult U _ = U

type family MaybeJoin r s where
  MaybeJoin s s = s
  MaybeJoin U _ = U
  MaybeJoin _ U = U
  MaybeJoin _ _ = U

data GMaybe r a where
  GNothing ::               GMaybe F a
  GJust    ::          a -> GMaybe T a
  GDyn     :: GMaybe r a -> GMaybe U a

runGMaybe :: GMaybe r a -> Maybe a
runGMaybe GNothing = Nothing
runGMaybe (GJust x) = Just x
runGMaybe (GDyn x) = runGMaybe x

instance Show a => Show (GMaybe r a) where
  show (GJust x) = "GJust " ++ show x
  show GNothing = "GNothing"
  show (GDyn x) = show x

instance Subeffect GMaybe r r where
  sub = id
instance Subeffect GMaybe T U where
  sub = GDyn
instance Subeffect GMaybe F U where
  sub = GDyn

instance GFunctor GMaybe where
  fmapG f GNothing = GNothing
  fmapG f (GJust x) = GJust (f x)
  fmapG f (GDyn x) = GDyn (fmapG f x)

instance GBindable GMaybe F s where
  bindG GNothing _ = GNothing
instance GBindable GMaybe T s where
  bindG (GJust x) k = k x
instance GBindable GMaybe U F where
  bindG (GDyn x) _ = GNothing
instance GBindable GMaybe U T where
  bindG (GDyn GNothing) _ = GDyn GNothing
  bindG (GDyn (GJust x)) k = GDyn (k x)
instance GBindable GMaybe U U where
  bindG (GDyn GNothing) _ = GDyn GNothing
  bindG (GDyn (GJust x)) k = GDyn (k x)

instance GMonad GMaybe where
  type Unit GMaybe = T
  type Seq GMaybe e f = MaybeMult e f
  type Join GMaybe e f = MaybeJoin e f
  return x = GJust x