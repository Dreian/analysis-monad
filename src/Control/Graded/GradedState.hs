{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Control.Graded.GradedState where

import Prelude as P hiding (Monad(..))
import Control.Graded
import Control.Graded.Identity
import Control.Graded.Maybe
import Control.Graded.HistState
import Control.Graded.PermState
import Control.Graded.Trans.Identity
import Control.Graded.Trans.Maybe
import Control.Graded.Trans.PermState

class GMonad m => GradedState (s :: *) (m :: k -> * -> *) | m -> s where
  type Rd m :: k
  type Wr m :: k
  getG :: m (Rd m) s
  putG :: s -> m (Wr m) ()

instance GMonad m => GradedState s (PermStateT s m) where
  type Rd (PermStateT s m) = '(RO, Unit m)
  type Wr (PermStateT s m) = '(AW, Unit m)
  getG = ROStateT return
  putG s = AWStateT (return ((), s))

instance GradedState s (PermState s) where
  type Rd (PermState s) = RO
  type Wr (PermState s) = AW
  getG = ROState id
  putG s = AWState ((), s)

instance GradedState s (HistState s) where
  type Rd (HistState s) = Fin Zero
  type Wr (HistState s) = Fin (Succ Zero)
  getG = FinHistState (\s -> (s, FromVec VNil))
  putG s = FinHistState (\_ -> ((), FromVec (s:::VNil)))

instance GradedState s m => GradedState s (IdentityT m) where
  type Rd (IdentityT m) = '(S, Rd m)
  type Wr (IdentityT m) = '(S, Wr m)
  getG = IdentityT getG
  putG = IdentityT . putG

instance GradedState s m => GradedState s (GMaybeT m) where
  type Rd (GMaybeT m) = '(T, Rd m)
  type Wr (GMaybeT m) = '(T, Wr m)
  getG = GMaybeT (fmapG GJust getG)
  putG x = GMaybeT (fmapG GJust (putG x))
