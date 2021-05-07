open import Level
open import Data.Product
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)


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
 1+ : Nat → Nat

{-# BUILTIN NATURAL Nat #-}

{-
plus : Nat × Nat → Nat
plus (n , zero') = n
plus (n , succ m) = succ (plus (n , m))

mult : Nat × Nat → Nat
mult (n , zero') = zero'
mult (n , succ m) = plus (n , mult (n , m))

-}
_+_ : Nat → Nat → Nat
n + 0 = n
n + (1+ m) = 1+ (n + m)

_*_ : Nat → Nat → Nat
n * 0 = 0
n * (1+ m) = n + (n * m)

fact : Nat → Nat
fact 0 = 1
fact (1+ n) = (1+ n) * (fact n)

fib : Nat → Nat
fib 0 = 0
fib (1+ 0) = 1
fib (1+ (1+ n)) = (fib n) + (fib (1+ n))

foldn : {A : Set} → A → (A → A) → (Nat → A)
foldn c h 0 = c
foldn c h (1+ n) = h (foldn c h n)

foldn1+is+ : (m n : Nat) → (m + n) ≡ ((foldn m 1+) n)
foldn1+is+ m 0 = refl
foldn1+is+ m (1+ n) = cong 1+ (foldn1+is+ m n)


foldn+is* : (m n : Nat) → m * n ≡ (foldn 0 (λ x → m + x)) n
foldn+is* m 0 = refl
foldn+is* m (1+ n) = cong (λ x → m + x) (foldn+is* m n)

expn : Nat → Nat → Nat
expn m = foldn 1 (λ n →  m * n)


outl : {A B : Set} → (A × B) → A
outl (fst , snd) = fst

outr : {A B : Set} → (A × B) → B
outr (fst , snd) = snd

f1 : (Nat × Nat) → Nat × Nat
f1 (m , n) = (1+ m , (1+ m) * n)

rec-× : {A B C D : Set} → (f : A → B) → (g : C → D) → ((A × C) -> (B × D))
rec-× f g (a , c) = (f a , g c)

outrFoldnIsFact : (n : Nat) → (foldn (0 , 1) f1 n) ≡ (n , fact n)
outrFoldnIsFact zero' = refl
outrFoldnIsFact (1+ n) rewrite (outrFoldnIsFact n) = refl

-- 1.3 Lists

data listr (A : Set l) : Set l where
 nil : listr A
 cons : A → listr A → listr A

data listl (A : Set l) : Set l where
 nil : listl A
 snoc : listl A → A → listl A

snocr : {A : Set} → listr A → A → listr A
snocr nil a = cons a nil
snocr (cons a0 as) a1 = cons a0 (snocr as a1)

convert : {A : Set} → listl A → listr A
convert nil = nil
convert (snoc xs x) = snocr (convert xs) x

_++_ : {A : Set} → listl A → listl A → listl A
xs ++ nil = xs
xs ++ snoc ys x = snoc (xs ++ ys) x

++-assoc : {A : Set} → (xs ys zs : listl A) → (xs ++ (ys ++ zs)) ≡ ((xs ++ ys) ++ zs)
++-assoc xs ys nil = refl
++-assoc xs ys (snoc zs x) = cong (λ y → snoc y x) (++-assoc xs ys zs)

listrF : {A B : Set} → (A → B) → listr A → listr B
listrF f nil = nil
listrF f (cons x as) = cons (f x) (listrF f as)

foldr : {A B : Set} → B → (A → B → B) → (listr A → B)
foldr c h nil = c
foldr c h (cons a as) = h a (foldr c h as)

