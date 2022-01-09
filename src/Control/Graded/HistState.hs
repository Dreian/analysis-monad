{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Control.Graded.HistState where

import Prelude as P hiding (Monad(..))
import Control.Graded

data Nat = Succ Nat | Zero

class NatLE (m :: Nat) (n :: Nat)
instance NatLE Zero (Succ n)
instance NatLE m n => NatLE (Succ m) (Succ n)

data a :~: b where
   Refl :: a :~: a

data NatI (n :: Nat) where
  ZI :: NatI Zero
  SI :: NatI n -> NatI (Succ n)

data Vec (n :: Nat) a where
  VNil  :: Vec Zero a
  (:::) :: {vHead :: a, vTail :: Vec n a} -> Vec (Succ n) a

infixr 5 :::

data VecTo (n :: Nat) a where
  FromVec :: Vec n a              -> VecTo n a
  Ext     :: {unExt :: VecTo n a} -> VecTo (Succ n) a

vecAsList :: Vec n a -> [a]
vecAsList VNil     = []
vecAsList (x:::xs) = x : vecAsList xs

vecToList :: VecTo n a -> [a]
vecToList (FromVec v) = vecAsList v
vecToList (Ext vecto) = vecToList vecto

data NatInf = Fin Nat | Inf

data NatInfI (n :: NatInf) where
  FinI :: NatI m -> NatInfI (Fin m)
  InfI :: NatInfI Inf

type family AddNat (m :: Nat) (n :: Nat) :: Nat where
  AddNat Zero n     = n
  AddNat (Succ m) n = Succ (AddNat m n)

-- inductive proof of: n + Z = n  
sumZeroRight :: NatI n -> (AddNat n Zero) :~: n
sumZeroRight ZI = Refl
sumZeroRight (SI n') = case sumZeroRight n' of
  Refl -> Refl

-- inductive proof of: n + S m = S (n + m)
sumSuccRight :: NatI n -> NatI m -> (AddNat n (Succ m)) :~: Succ (AddNat n m)
sumSuccRight ZI _ = Refl
sumSuccRight (SI n') m  = case sumSuccRight n' m of
  Refl -> Refl

-- inductive proof of commutativity: n + m = m + n
sumComm :: NatI n -> NatI m -> (AddNat n m) :~: (AddNat m n)
sumComm ZI m = case sumZeroRight m of Refl -> Refl
sumComm (SI n') m = case (sumComm n' m, sumSuccRight m n') of
  (Refl, Refl) -> Refl

-- inductive proof of commutativity of inf: n + m = m + n
sumCommInf :: NatInfI n -> NatInfI m -> (AddInf n m) :~: (AddInf m n)
sumCommInf InfI _ = Refl
sumCommInf _ InfI = Refl
sumCommInf (FinI m) (FinI n) = case sumComm m n of
  Refl -> Refl

vecLengthI :: Vec n a -> NatI n
vecLengthI VNil = ZI
vecLengthI (_:::xs) = SI (vecLengthI xs)

vecToLengthI :: VecTo n a -> NatI n
vecToLengthI (FromVec l) = vecLengthI l
vecToLengthI (Ext l)     = SI (vecToLengthI l)

(+++) :: Vec m a -> Vec n a -> Vec (AddNat m n) a
VNil     +++ l = l
(x:::xs) +++ l = x:::(xs +++ l)

infixr 5 +++

(<++>) :: VecTo m a -> VecTo n a -> VecTo (AddNat m n) a
(FromVec xs) <++> (FromVec ys) = FromVec (xs +++ ys)
(FromVec xs) <++> (Ext ys)     = case sumSuccRight (vecLengthI xs) (vecToLengthI ys) of
                                   Refl -> Ext ((FromVec xs) <++> ys)
(Ext xs)     <++> vec          = Ext (xs <++> vec)

infixr 5 <++>

type family AddInf (m :: NatInf) (n :: NatInf) :: NatInf where
  AddInf n Inf           = Inf
  AddInf Inf n           = Inf
  AddInf (Fin m) (Fin n) = Fin (AddNat m n)

type family MaxNat (m :: Nat) (n :: Nat) :: Nat where
  MaxNat Zero n            = n
  MaxNat m Zero            = m
  MaxNat (Succ m) (Succ n) = Succ (MaxNat m n)

type family JoinInf (m :: NatInf) (n :: NatInf) :: NatInf where
  JoinInf Inf _             = Inf
  JoinInf _ Inf             = Inf
  JoinInf (Fin m) (Fin n)   = Fin (MaxNat m n)

data HistState s (f :: NatInf) a where
  FinHistState :: {runFinHistState :: s -> (a, VecTo n s)} -> HistState s (Fin n) a
  InfHistState :: {runInfHistState :: s -> (a, [s])}       -> HistState s Inf a

runHistState :: HistState s n a -> s -> (a, [s])
runHistState (FinHistState c) s = let (r, l) = c s in (r, vecToList l)
runHistState (InfHistState c) s = c s

class Paddable (m :: Nat) (n :: Nat) where
  padExt :: VecTo m a -> VecTo n a

instance Paddable n n where
  padExt v = v
instance Paddable (Succ m) n => Paddable m n where
  padExt (Ext v) = padExt v

instance Subeffect (HistState s) r r where
  sub = id
instance Subeffect (HistState s) (Fin n) Inf where
  sub (FinHistState c) = InfHistState (\s -> let (r, l) = c s in (r, vecToList l)) 
instance (NatLE m n, Paddable m n) => Subeffect (HistState s) (Fin m) (Fin n) where
  sub (FinHistState c) = FinHistState (\s -> let (r, l) = c s in (r, padExt l))

instance GBindable (HistState s) (Fin m) (Fin n) where
  bindG (FinHistState c) k = FinHistState (\s -> 
    let (x, l1) = c s in
    let FinHistState c' = k x in
    let (r, l2) = c' (head (vecToList l1 ++ [s])) in
      (r, case sumCommInf (FinI (vecToLengthI l2)) (FinI (vecToLengthI l1)) of
            Refl -> l2 <++> l1))
instance GBindable (HistState s) (Fin m) Inf where
  bindG (FinHistState c) k = InfHistState (\s ->
    let (x, l1) = c s in
    let InfHistState c' = k x in
    let (r, l2) = c' (head (vecToList l1 ++ [s])) in
      (r, l2 ++ vecToList l1))
instance GBindable (HistState s) Inf (Fin n) where
  bindG (InfHistState c) k = InfHistState (\s ->
    let (x, l1) = c s in
    let FinHistState c' = k x in
    let (r, l2) = c' (head (l1 ++ [s])) in
      (r, vecToList l2 ++ l1))
instance GBindable (HistState s) Inf Inf where
  bindG (InfHistState c) k = InfHistState (\s ->
    let (x, l1) = c s in
    let InfHistState c' = k x in 
    let (r, l2) = c' (head (l1 ++ [s])) in
      (r, l2 ++ l1))

instance GFunctor (HistState s) where
  fmapG f (FinHistState c) = FinHistState (\s -> let (r, l) = c s in (f r, l))
  fmapG f (InfHistState c) = InfHistState (\s -> let (r, l) = c s in (f r, l))

instance GMonad (HistState s) where
  type Unit (HistState s) = Fin Zero
  type Seq (HistState s) e f = AddInf f e
  type Join (HistState s) e f = JoinInf e f
  return x = FinHistState (\s -> (x, FromVec VNil))

nopHistState :: HistState s (Fin Zero) ()
nopHistState = return ()
