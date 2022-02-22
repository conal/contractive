{-# OPTIONS --guardedness #-}

module BinTree2 where

open import Data.Product as × hiding (map; zip)

private variable A B : Set

two : Set → Set
two A = A × A

twice : (A → B) → (two A → two B)
twice f = ×.map f f
-- twice f (x , y) = f x , f y

record T A : Set where
  coinductive
  constructor Node
  field
    get : A
    sub : T (two A)

open T

map : (A → B) → T A → T B
get (map f t) = f (get t)
sub (map f t) = map (twice f) (sub t)

open import Data.Bool hiding (_<_; T)
open import Data.List as [] hiding (map; zip; unzip)

proj : Bool → two A → A
proj false = proj₁
proj true  = proj₂

_!_ : T A → List Bool → A
z !    []    = get z
z ! (i ∷ is) = map (proj i) (sub z) ! is

open import Data.Nat
open import Relation.Binary.PropositionalEquality

infix 4 _≈[_]_
_≈[_]_ : T A → ℕ → T A → Set
s ≈[ n ] t = ∀ p → length p < n → s ! p ≡ t ! p


record Gen (A B : Set) : Set where
  coinductive
  constructor Step
  field
    output : B
    cont   : A → Gen (two A) (two B)
