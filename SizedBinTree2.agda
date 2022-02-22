{-# OPTIONS --guardedness --sized-types #-}
-- Coinductive, size-typed, prezipped binary trees

module SizedBinTree2 where

open import Data.Product as × hiding (map; zip)

open import Size

record T i A : Set where
  coinductive
  constructor Node
  field
    get : A
    sub : {j : Size< i} → T j (A × A)

open T

private variable
  A B : Set
  i j : Size

two : Set → Set
two A = A × A

map : (A → B) → T i A → T i B
get (map f t) = f (get t)
sub (map f t) = map (×.map f f) (sub t)

open import Data.Bool hiding (_<_; T)
open import Data.List as [] hiding (map; zip; unzip)

proj : Bool → two A → A
proj false = proj₁
proj true  = proj₂

_!_ : T ∞ A → List Bool → A
z !    []    = get z
z ! (i ∷ is) = map (proj i) (sub z) ! is

open import Data.Nat
open import Relation.Binary.PropositionalEquality

infix 4 _≈[_]_
_≈[_]_ : T ∞ A → ℕ → T ∞ A → Set
s ≈[ n ] t = ∀ p → length p < n → s ! p ≡ t ! p

contractive : (T ∞ A → T ∞ B) → Set
contractive f = ∀ n s t → s ≈[ n ] t → f s ≈[ suc n ] f t 

record Gen i (A B : Set) : Set where
  coinductive
  constructor Step
  field
    out  : B
    cont : {j : Size< i} → A → Gen j (two A) (two B)

open Gen

gen : Gen i A B → T i A → T i B
get (gen g t) = out g
sub (gen g t) = gen (cont g (get t)) (sub t)

-- gen-contractive : (g : Gen ∞ A B) → contractive (gen g)
-- gen-contractive g n s t s≈ₙt p |p|≤n = {!!}

-- infix 4 _≈[_]_
-- _≈[_]_ : T ∞ A → ℕ → T ∞ A → Set
-- s ≈[ n ] t = ∀ p → length p < n → s ! p ≡ t ! p

-- contractive : (T ∞ A → T ∞ B) → Set
-- contractive f = ∀ n s t → s ≈[ n ] t → f s ≈[ suc n ] f t 
