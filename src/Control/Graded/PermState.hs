{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}

module Control.Graded.PermState where

import Prelude as P hiding (Monad(..))
import Control.Graded

data Perm = Pure | RO | AW | WO | RW

type family PermJoin r s where
  PermJoin s s = s
  PermJoin Pure AW = WO
  PermJoin Pure s = s
  PermJoin AW Pure = WO
  PermJoin s Pure = s
  PermJoin AW WO = WO
  PermJoin WO AW = WO
  PermJoin _ _ = RW

type family PermSeq r s where
  PermSeq s s = s
  PermSeq Pure s = s
  PermSeq s Pure = s
  PermSeq AW _ = AW
  PermSeq RO _ = RW
  PermSeq RW _ = RW
  PermSeq WO RO = RW
  PermSeq WO RW = RW
  PermSeq WO AW = AW
  
data PermState s (f :: Perm) a where
  PureState :: {runPureState :: a}            -> PermState s Pure a
  ROState   :: {runROState   :: s -> a}       -> PermState s RO   a
  AWState   :: {runAWState   :: (a, s)}       -> PermState s AW   a
  WOState   :: {runWOState   :: (a, Maybe s)} -> PermState s WO   a
  RWState   :: {runRWState   :: s -> (a, s)}  -> PermState s RW   a

runPermState :: PermState s f a -> s -> (a, s)
runPermState (PureState x)    s = (x, s)
runPermState (ROState f)      s = (f s, s)
runPermState (AWState (x, s)) _ = (x, s)
runPermState (WOState (x, m)) s = case m of
  Nothing -> (x, s)
  Just y  -> (x, y)
runPermState (RWState f)      s = f s

instance Subeffect (PermState s) r r where
  sub = id
instance Subeffect (PermState s) Pure RO where
  sub (PureState x) = ROState (const x)
instance Subeffect (PermState s) Pure WO where
  sub (PureState x) = WOState (x, Nothing)
instance Subeffect (PermState s) Pure RW where
  sub (PureState x) = RWState (\s -> (x, s))
instance Subeffect (PermState s) AW WO where
  sub (AWState (x, s)) = WOState (x, Just s)
instance Subeffect (PermState s) AW RW where
  sub (AWState (x, s)) = RWState (const (x, s))
instance Subeffect (PermState s) RO RW where
  sub (ROState x) = RWState (\s -> (x s, s))
instance Subeffect (PermState s) WO RW where
  sub (WOState (x, Just s))  = RWState (const (x, s))
  sub (WOState (x, Nothing)) = RWState (\s -> (x, s))

instance GBindable (PermState s) Pure r where
  bindG (PureState x) k = k x
instance GBindable (PermState s) RO Pure where
  bindG (ROState f) k = ROState (runPureState . k . f)
instance GBindable (PermState s) RO RO where
  bindG (ROState f) k = ROState (\s -> (runROState (k (f s))) s)
instance GBindable (PermState s) RO AW where
  bindG (ROState f) k = RWState (runAWState . k . f)
instance GBindable (PermState s) RO WO where
  bindG (ROState f) k = RWState (\s -> let (r, s') = runWOState (k (f s)) in case s' of
    Just y -> (r, y)
    Nothing -> (r, s))
instance GBindable (PermState s) RO RW where
  bindG (ROState f) k = RWState (\s -> runRWState (k (f s)) s)
instance GBindable (PermState s) AW Pure where
  bindG (AWState (x, s)) k = AWState (runPureState (k x), s)
instance GBindable (PermState s) AW RO where
  bindG (AWState (x, s)) k = AWState (runROState (k x) s, s)
instance GBindable (PermState s) AW AW where
  bindG (AWState (x, s)) k = k x
instance GBindable (PermState s) AW WO where
  bindG (AWState (x, s)) k = AWState (let (r, s') = runWOState (k x) in case s' of
    Just y -> (r, y)
    Nothing -> (r, s))
instance GBindable (PermState s) AW RW where
  bindG (AWState (x, s)) k = AWState (runRWState (k x) s)
instance GBindable (PermState s) WO Pure where
  bindG (WOState (x, s)) k = WOState (runPureState (k x), s)
instance GBindable (PermState s) WO RO where
  bindG (WOState (x, Just s)) k = RWState (\s' -> (runROState (k x) s, s))
  bindG (WOState (x, Nothing)) k = RWState (\s' -> (runROState (k x) s', s'))
instance GBindable (PermState s) WO AW where
  bindG (WOState (x, _)) k = k x
instance GBindable (PermState s) WO WO where
  bindG (WOState (x, Just s)) k = WOState (let (r, s') = runWOState (k x) in case s' of
    Just y -> (r, Just y)
    Nothing -> (r, Just s))
  bindG (WOState (x, Nothing)) k = k x
instance GBindable (PermState s) WO RW where
  bindG (WOState (x, Just s)) k = RWState (\s' -> runRWState (k x) s)
  bindG (WOState (x, Nothing)) k = k x
instance GBindable (PermState s) RW Pure where
  bindG (RWState f) k = RWState (\s -> let (x, s') = f s in (runPureState (k x), s'))
instance GBindable (PermState s) RW RO where
  bindG (RWState f) k = RWState (\s -> let (x, s') = f s in (runROState (k x) s', s'))
instance GBindable (PermState s) RW AW where
  bindG (RWState f) k = RWState (\s -> let (x, _) = f s in runAWState (k x))
instance GBindable (PermState s) RW WO where
  bindG (RWState f) k = RWState (\s -> let (x, s') = f s in let (r, s'') = runWOState (k x) in case s'' of
    Just y -> (r, y)
    Nothing -> (r, s'))
instance GBindable (PermState s) RW RW where
  bindG (RWState f) k = RWState (\s -> let (x, s') = f s in runRWState (k x) s')
  
instance GFunctor (PermState s) where
  fmapG f (PureState x) = PureState (f x)
  fmapG f (ROState f') = ROState (\s -> f (f' s))
  fmapG f (AWState (x, s)) = AWState (f x, s)
  fmapG f (WOState (x, s)) = WOState (f x, s)
  fmapG f (RWState f') = RWState (\s -> (\(x, y) -> (f x, y)) (f' s))

instance GMonad (PermState s) where
  type Unit (PermState s) = Pure
  type Seq (PermState s) e f = PermSeq e f
  type Join (PermState s) e f = PermJoin e f
  return = PureState

nopPermState :: PermState s Pure ()
nopPermState = return ()
