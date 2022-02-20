{-# OPTIONS --guardedness #-}

module Stream where

record S A : Set where
  coinductive
  constructor _◃_ 
  field
    head : A
    tail : S A

open S

private variable A B C : Set

open import Data.Nat
open import Data.Vec as v using (Vec; []; _∷_)

take : S A → {n : ℕ} → Vec A n
take s {zero} = []
take s {suc n} = head s ∷ take (tail s) {n}

open import Relation.Binary.PropositionalEquality ; open ≡-Reasoning

infix 4 _≈[_]_
_≈[_]_ : S A → ℕ → S A → Set
s ≈[ n ] t = take s {n} ≡ take t

infix 0 _→ˢ_
_→ˢ_ : Set → Set → Set
A →ˢ B = S A → S B

-- Influence of inputs are delayed by at least d steps
delayed : ℕ → (A →ˢ B) → Set
delayed d f = ∀ {n s t} → s ≈[ n ] t → f s ≈[ d + n ] f t

open import Function using (_∘_)

open import Data.Nat.Properties

delayed-∘ : ∀ {d e} {f : A →ˢ B} {g : B →ˢ C} →
  delayed e g → delayed d f → delayed (e + d) (g ∘ f)

delayed-∘ {d = d} {e} delayed-g delayed-f {n = n} rewrite +-assoc e d n =
  delayed-g ∘ delayed-f

causal : (A →ˢ B) → Set
causal = delayed 0

contractive : (A →ˢ B) → Set
contractive = delayed 1

open import Data.Product using (∃; Σ; _,_)

-- Stream functions delayed by d
infix 0 _→[_]_
_→[_]_ : Set → ℕ → Set → Set
A →[ d ] B = Σ (A →ˢ B) (delayed d)

infix 0 _→₀_ _→₁_
_→₀_ _→₁_ : Set → Set → Set
A →₀ B = A →[ 0 ] B  -- causal
A →₁ B = A →[ 1 ] B  -- contractive

map : (A → B) → (A →ˢ B)
head (map f s) = f (head s)
tail (map f s) = map f (tail s)

open import Data.Bool

invˢ : Bool →ˢ Bool
invˢ = map not

delayˢ : A → A →ˢ A
delayˢ = _◃_

take-map : ∀ (f : A → B) s {n} → take (map f s) {n} ≡ v.map f (take s)
take-map f s {zero } = refl
take-map f s {suc n} rewrite take-map f (tail s) {n} = refl

-- take-map s f {suc n} =
--   begin
--     take (map f s)
--   ≡⟨⟩
--     f (head s) ∷ take (map f (tail s))
--   ≡⟨ cong (f (head s) ∷_) (take-map (tail s) f) ⟩
--     f (head s) ∷ v.map f (take (tail s))
--   ≡⟨⟩
--     v.map f (take s)
--   ∎

map≈ : ∀ (f : A → B) → causal (map f)
map≈ f {zero } s∼t = refl
map≈ f {suc n} {s = s} {t} s∼t =
  begin
    take (map f s)
  ≡⟨ take-map f s ⟩
    v.map f (take s)
  ≡⟨ cong (v.map f) s∼t ⟩
    v.map f (take t)
  ≡˘⟨ take-map f t ⟩
    take (map f t)
  ∎

delay-contractive : ∀ (a : A) → contractive (delayˢ a)
delay-contractive _ {n = zero } _ = refl
delay-contractive _ {n = suc n} s∼t rewrite s∼t = refl

-- delay-contractive a {n = suc n} s t s∼t =
--   begin
--     take (a ◃ s)
--   ≡⟨⟩
--     a ∷ head s ∷ take (tail s)
--   ≡⟨ cong (a ∷_) s∼t ⟩
--     a ∷ head t ∷ take (tail t)
--   ≡⟨⟩
--     take (a ◃ t)
--   ∎

delayᶜ : A → A →₁ A
delayᶜ a = delayˢ a , delay-contractive a

causal-delay-contractive : ∀ (f : A →ˢ B) (a : A) → causal f →
  contractive (f ∘ delayˢ a)
causal-delay-contractive f a causal-f = delayed-∘ causal-f (delay-contractive a)
