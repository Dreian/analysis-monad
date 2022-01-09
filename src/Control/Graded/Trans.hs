{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}

module Control.Graded.Trans where

import Control.Graded

class GMonadTrans (t :: (k -> * -> *) -> (k', k) -> * -> *) where
  type IdG t :: k'
  liftG      :: GMonad m => m s a -> t m '(IdG t, s) a