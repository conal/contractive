{-# OPTIONS --guardedness --sized-types #-}
-- Coinductive, size-typed binary trees

module SizedBinTree where

open import Size

record T i A : Set where
  coinductive
  constructor Node
  field
    get : A
    left right : {j : Size< i} → T j A

open T

private variable
  A B : Set
  i j : Size

map : (A → B) → T i A → T i B
get   (map f t) = f (get t)
left  (map f t) = map f (left t)
right (map f t) = map f (right t)

open import Data.Bool hiding (_<_; T)
open import Data.List as [] hiding (map; zip; unzip)

_!_ : T ∞ A → List Bool → A
z ! [] = get z
z ! (false ∷ is) = left  z ! is
z ! (true  ∷ is) = right z ! is

open import Data.Nat
open import Relation.Binary.PropositionalEquality

infix 4 _≈[_]_
_≈[_]_ : T ∞ A → ℕ → T ∞ A → Set
s ≈[ n ] t = ∀ p → length p < n → s ! p ≡ t ! p

-- codata Gen A B = Step {output : B; cont : A → Gen (A × A) (B × B)}.

open import Data.Product as × hiding (map; zip)

record Gen i (A B : Set) : Set where
  coinductive
  -- inductive ; eta-equality
  constructor Step
  field
    output : B
    cont   : {j : Size< i} → A → Gen j (A × A) (B × B)

open Gen

unzip : T i (A × B) → T i A × T i B
unzip t = map proj₁ t , map proj₂ t

zip : T i A → T i B → T i (A × B)
get   (zip s t) = get s , get t
left  (zip s t) = zip (left  s) (left  t)
right (zip s t) = zip (right s) (right t)

-- Termination checking fail.
-- Try fixing with sized types.

gen : Gen i A B → T i A → T i B
get   (gen g t) = output g
left  (gen g t) = map proj₁ (gen (cont g (get t)) (zip (left t) (right t)))
right (gen g t) = map proj₂ (gen (cont g (get t)) (zip (left t) (right t)))
