{-# OPTIONS --guardedness #-}
-- Coinductive binary trees

module BinTree where

record T A : Set where
  coinductive
  constructor Node
  field
    get : A
    left right : T A

open T

private variable A B : Set

map : (A → B) → T A → T B
get   (map f t) = f (get t)
left  (map f t) = map f (left t)
right (map f t) = map f (right t)

open import Data.Bool hiding (_<_; T)
open import Data.List as [] hiding (map; zip; unzip)

_!_ : T A → List Bool → A
z ! [] = get z
z ! (false ∷ is) = left  z ! is
z ! (true  ∷ is) = right z ! is

open import Data.Nat
open import Relation.Binary.PropositionalEquality

infix 4 _≈[_]_
_≈[_]_ : T A → ℕ → T A → Set
s ≈[ n ] t = ∀ p → length p < n → s ! p ≡ t ! p

-- codata Gen A B = Step {output : B; cont : A → Gen (A × A) (B × B)}.

open import Data.Product as × hiding (map; zip)

record Gen (A B : Set) : Set where
  coinductive
  -- inductive ; eta-equality
  constructor Step
  field
    output : B
    cont   : A → Gen (A × A) (B × B)

open Gen

unzip : T (A × B) → T A × T B
unzip t = map proj₁ t , map proj₂ t

zip : T A → T B → T (A × B)
get   (zip s t) = get s , get t
left  (zip s t) = zip (left  s) (left  t)
right (zip s t) = zip (right s) (right t)

-- Termination checking fail.
-- Try fixing with sized types.

-- gen : Gen A B → T A → T B
-- get   (gen g t) = output g
-- left  (gen g t) = map proj₁ (gen (cont g (get t)) (zip (left t) (right t)))
-- right (gen g t) = {!!}

-- gen : Gen A B → T A → T B
-- get   (gen (Step b k) t) = b
-- left  (gen (Step b k) t) = map proj₁ (gen (k (get t)) (zip (left t) (right t)))
-- right (gen (Step b k) t) = {!!} -- map proj₂ (gen (k (get t)) (zip (left t) (right t)))

-- gen (Step b f) (Node a t₁ t₂) = Node b u₁ u₂
--  where (u₁, u₂) = unzip (gen (f a) (zip t₁ t₂))
