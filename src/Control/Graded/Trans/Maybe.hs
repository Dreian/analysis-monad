{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Control.Graded.Trans.Maybe where

import Prelude hiding (Monad(..))
import Control.Graded
import Control.Graded.Maybe
import Control.Graded.Trans

data GMaybeT m r a where
  GMaybeT :: {runGMaybeT :: m f (GMaybe e a)} -> GMaybeT m '(e, f) a

instance (Subeffect m f f') => Subeffect (GMaybeT m) '(e, f) '(e, f') where
  sub (GMaybeT x) = GMaybeT (sub x)
instance (Subeffect m f f', Subeffect GMaybe T U, GFunctor m) => Subeffect (GMaybeT m) '(T, f) '(U, f') where
  sub (GMaybeT x) = GMaybeT (sub (fmapG sub x))
instance (Subeffect m f f', Subeffect GMaybe F U, GFunctor m) => Subeffect (GMaybeT m) '(F, f) '(U, f') where
  sub (GMaybeT x) = GMaybeT (sub (fmapG sub x))

instance (GFunctor GMaybe, GFunctor m) => GFunctor (GMaybeT m) where
  fmapG f (GMaybeT x) = GMaybeT (fmapG (fmapG f) x)

type family MaybeTMult (m :: k -> * -> *) (r :: (MaybeGr, k)) (s :: (MaybeGr, k)) where
  MaybeTMult m '(F, f) _ = '(F, f)
  MaybeTMult m '(T, f) '(s, f') = '(s, Seq m f f')
  MaybeTMult m '(U, f) '(F, f') = '(F, Seq m f (Join m f' (Unit m)))
  MaybeTMult m '(U, f) '(_, f') = '(U, Seq m f (Join m f' (Unit m)))

instance (GBindable GMaybe F e', GBindable m f (Unit m), LeftId m f)
 => GBindable (GMaybeT m) '(F, f) '(e', f') where
  bindG (GMaybeT x) k = GMaybeT $ x >> return GNothing
instance (GBindable GMaybe T e', GBindable m f f')
 => GBindable (GMaybeT m) '(T, f) '(e', f') where
  bindG (GMaybeT x) k = GMaybeT $ x >>= \r -> let GJust y = r in runGMaybeT (k y)

-- helper functions for handling bind: used for all cases where the grades do not match
helperUF :: (GMonad m, JoinUpper m f' (Unit m)) => GMaybe U a -> (a -> GMaybeT m '(F, f') b) -> GMaybeT m '(F, Join m f' (Unit m)) b
helperUF (GDyn y) k' = GMaybeT $ case y of
  GNothing -> sub (return GNothing)
  GJust z  -> sub (runGMaybeT (k' z))
instance (GBindable GMaybe U F, GBindable m f (Join m f' (Unit m)), JoinUpper m f' (Unit m))
 => GBindable (GMaybeT m) '(U, f) '(F, f') where
  bindG (GMaybeT x) k = GMaybeT $ x >>= \r -> runGMaybeT (helperUF r k)

helperUT :: (GMonad m, JoinUpper m f' (Unit m)) => GMaybe U a -> (a -> GMaybeT m '(T, f') b) -> GMaybeT m '(U, Join m f' (Unit m)) b
helperUT (GDyn y) k' = GMaybeT $ case y of
  GNothing -> sub (return (GDyn GNothing))
  GJust z  -> sub (fmapG GDyn (runGMaybeT (k' z)))
instance (GBindable GMaybe U T, GBindable m f (Join m f' (Unit m)), JoinUpper m f' (Unit m))
 => GBindable (GMaybeT m) '(U, f) '(T, f') where
  bindG (GMaybeT x) k = GMaybeT $ x >>= \r -> runGMaybeT (helperUT r k)

helperUU :: (GMonad m, JoinUpper m f' (Unit m)) => GMaybe U a -> (a -> GMaybeT m '(U, f') b) -> GMaybeT m '(U, Join m f' (Unit m)) b
helperUU (GDyn y) k' = GMaybeT $ case y of
  GNothing -> sub (return (GDyn GNothing))
  GJust z  -> sub (runGMaybeT (k' z))
instance (GBindable GMaybe U U, GBindable m f (Join m f' (Unit m)), JoinUpper m f' (Unit m))
 => GBindable (GMaybeT m) '(U, f) '(U, f') where
  bindG (GMaybeT x) k = GMaybeT $ x >>= \r -> runGMaybeT (helperUU r k)

instance GMonad m => GMonad (GMaybeT m :: (MaybeGr, k) -> * -> *) where
  type Unit (GMaybeT m) = '(T, Unit m)
  type Seq (GMaybeT m) r s = MaybeTMult m r s
  type Join (GMaybeT m) '(e, f) '(e', f') = '(MaybeJoin e e', Join m f f')
  return x = GMaybeT (return (GJust x))

instance GMonadTrans GMaybeT where
  type IdG GMaybeT = 'T
  liftG = GMaybeT . (fmapG GJust)
