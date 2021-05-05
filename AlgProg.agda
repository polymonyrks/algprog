open import Level
open import Data.Product
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality using (_≡_; refl)


module AlgProg where

-- 1.1 Datatypes

private
 variable
  l : Level

data Bool : Set where
 false : Bool
 true : Bool

data Char : Set where
 ca : Char
 cb : Char
 cc : Char

data Either : Set where
 bool : Bool → Either
 char : Char → Either

data Both : Set where
 tuple : Bool × Char → Both

not : Bool → Bool
not false = true
not true = false

switch : Both → Both
switch (tuple (b , c)) = tuple (not b , c)

and : (Bool × Bool) → Bool
and (false , _) = false
and (true , b) = b

cand : Bool → Bool → Bool
cand false _ = false
cand true b = b

curry' : {A B C : Set} → (B → (C → A)) → ((B × C) → A)
curry' f (b , c) = f b c

data maybe (A : Set l) : Set l where
 nothing : maybe A
 just : (x : A) → maybe A


-- 1.2 Natural Numbers

data Nat : Set where
 zero' : Nat
 succ : Nat → Nat

plus : Nat × Nat → Nat
plus (n , zero') = n
plus (n , succ m) = succ (plus (n , m))


mult : Nat × Nat → Nat
mult (n , zero') = zero'
mult (n , succ m) = plus (n , mult (n , m))
