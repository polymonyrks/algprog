open import Relation.Nullary
open import Relation.Binary.PropositionalEquality using (_≡_; refl)


module AlgProg where

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
 tuple : Bool → Char → Both

not : Bool → Bool
not false = true
not true = false

switch : Both → Both
switch (tuple b c) = tuple (not b) c
