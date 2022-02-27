{-# OPTIONS --guardedness #-}

module StreamTake where

open import Function using (_∘_; id; const)
open import Data.Product as × using (Σ; ∃; _×_; _,_; proj₁; proj₂)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Vec as v using (Vec; []; _∷_)
open import Data.Vec.Properties

open import Relation.Binary.PropositionalEquality ; open ≡-Reasoning

private variable
  A B C D : Set
  m n d e : ℕ

record Stream A : Set where
  coinductive
  constructor _◃_ 
  field
    head : A
    tail : Stream A

open Stream

take : (n : ℕ) → Stream A → Vec A n
take  zero   s = []
take (suc n) s = head s ∷ take n (tail s)

-- Usually n can be inferred in take, but explicit n yields clearer proofs.

-- Stream functions
infix 0 _→ˢ_
_→ˢ_ : Set → Set → Set
A →ˢ B = Stream A → Stream B

private variable fˢ gˢ hˢ : A →ˢ B

map : (A → B) → (A →ˢ B)
head (map f s) = f (head s)
tail (map f s) = map f (tail s)

take-map : ∀ (f : A → B) s {n} → take n (map f s) ≡ v.map f (take n s)
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

zip : Stream A × Stream B → Stream (A × B)
head (zip (xs , ys)) = head xs , head ys
tail (zip (xs , ys)) = zip (tail xs , tail ys)

take-zip : ∀ ((s , t) : Stream A × Stream B) {n} →
  take n (zip (s , t)) ≡ v.zip (take n s) (take n t)
take-zip (s , t) {zero } = refl
take-zip (s , t) {suc n} rewrite take-zip (tail s , tail t) {n} = refl

unzip : Stream (A × B) → Stream A × Stream B
unzip zs = map proj₁ zs , map proj₂ zs

infixr 7 _⊗_
_⊗_ : (A →ˢ C) → (B →ˢ D) → (A × B →ˢ C × D)
f ⊗ g = zip ∘ ×.map f g ∘ unzip

infix 4 _≡[_]_
_≡[_]_ : Stream A → ℕ → Stream A → Set
s ≡[ n ] t = take n s ≡ take n t

≡[≤] : ∀ {s t : Stream A} → m ≤ n → s ≡[ n ] t → s ≡[ m ] t
≡[≤] z≤n s∼ₙt = refl
≡[≤] {s = s} {t} (s≤s {m} m≤n) s∼ₙt with heads≡ , tails≡ ← ∷-injective s∼ₙt =
  begin
    take (suc m) s
  ≡⟨⟩
    head s ∷ take m (tail s)
  ≡⟨ cong₂ _∷_ heads≡ (≡[≤] {s = tail s} {tail t} m≤n tails≡) ⟩
    head t ∷ take m (tail t)
  ≡⟨⟩
    take (suc m) t
  ∎

-- Variation (unused)
≡[+] : {s : Stream A} {t : Stream A} → s ≡[ m + n ] t → s ≡[ m ] t
≡[+] s∼t = ≡[≤] (m≤m+n _ _) s∼t


-- Input influence lags by (at least) d steps.
infix 4 _↓_
_↓_ : (A →ˢ B) → ℕ → Set
f ↓ d = ∀ {n s t} → s ≡[ n ] t → f s ≡[ d + n ] f t

causal : (A →ˢ B) → Set
causal = _↓ 0

contractive : (A →ˢ B) → Set
contractive = _↓ 1

constant : (A →ˢ B) → Set
constant f = ∀ {d} → f ↓ d

≡-↓ : d ≡ e → fˢ ↓ d → fˢ ↓ e
≡-↓ refl = id

≤-↓ : e ≤ d → fˢ ↓ d → fˢ ↓ e
≤-↓ e≤d delayed-d {n} s∼t = ≡[≤] (+-monoˡ-≤ n e≤d) (delayed-d s∼t)

-- Constant functions never sense their inputs.
const↓ : {bs : Stream B} → constant {A = A} (const bs)
const↓ s∼t = refl

map↓ : ∀ (f : A → B) → causal (map f)
map↓ f {zero } s∼t = refl
map↓ f {suc n} {s = s} {t} s∼t =
  begin
    take (suc n) (map f s)
  ≡⟨ take-map f s ⟩
    v.map f (take (suc n) s)
  ≡⟨ cong (v.map f) s∼t ⟩
    v.map f (take (suc n) t)
  ≡˘⟨ take-map f t ⟩
    take (suc n) (map f t)
  ∎

delayˢ : A → A →ˢ A
delayˢ = _◃_

delay↓ : ∀ {a : A} → contractive (delayˢ a)
delay↓ {n = zero } _ = refl
delay↓ {n = suc n} s∼t rewrite s∼t = refl

-- delay↓ a {n = suc n} {s} {t} s∼t =
--   begin
--     take (suc (suc n)) (a ◃ s)
--   ≡⟨⟩
--     a ∷ head s ∷ take n (tail s)
--   ≡⟨ cong (a ∷_) s∼t ⟩
--     a ∷ head t ∷ take n (tail t)
--   ≡⟨⟩
--     take (suc (suc n)) (a ◃ t)
--   ∎

-- Sequential composition adds delays.
infixr 9 _∘↓_
_∘↓_ : gˢ ↓ e → fˢ ↓ d → gˢ ∘ fˢ ↓ e + d
_∘↓_ {e = e} {d = d} g↓ f↓ {n} rewrite +-assoc e d n = g↓ ∘ f↓

∘↓-map : gˢ ↓ e → (f : A → B) → (gˢ ∘ map f) ↓ e
∘↓-map {e = e} g↓ f = ≡-↓ (+-identityʳ e) (g↓ ∘↓ map↓ f)

-- Parallel composition with equal delays.
infixr 7 _⊗↓≡_
_⊗↓≡_ : fˢ ↓ d → gˢ ↓ d → fˢ ⊗ gˢ ↓ d
_⊗↓≡_ {fˢ = fˢ} {d = d} {gˢ = gˢ} f↓ g↓ {n} {s} {t} s∼t =
  begin
    take (d + n) ((fˢ ⊗ gˢ) s)
  ≡⟨⟩
    take (d + n) (zip (fˢ (map proj₁ s) , gˢ (map proj₂ s)))
  ≡⟨ take-zip _ ⟩
    v.zip (take (d + n) (fˢ (map proj₁ s))) (take (d + n) (gˢ (map proj₂ s)))
  ≡⟨ cong₂ v.zip (f↓ (map↓ proj₁ s∼t))
                 (g↓ (map↓ proj₂ s∼t)) ⟩
    v.zip (take (d + n) (fˢ (map proj₁ t))) (take (d + n) (gˢ (map proj₂ t)))
  ≡˘⟨ take-zip _ ⟩
    take (d + n) (zip (fˢ (map proj₁ t) , gˢ (map proj₂ t)))
  ≡⟨⟩
    take (d + n) ((fˢ ⊗ gˢ) t)
  ∎

-- Parallel composition with arbitrary delays
infixr 7 _⊗↓_
_⊗↓_ : fˢ ↓ d → gˢ ↓ e → (fˢ ⊗ gˢ) ↓ (d ⊓ e)
f↓ ⊗↓ g↓ = ≤-↓ (m⊓n≤m _ _) f↓ ⊗↓≡ ≤-↓ (m⊓n≤n _ _) g↓

-- Stream functions lagging by (at least) d
infix 0 _→[_]_
record _→[_]_ (A : Set) (d : ℕ) (B : Set) : Set where
  constructor mk
  field
    {f} : A →ˢ B
    f↓  : f ↓ d

-- Sequential composition
infixr 9 _∘ᵈ_
_∘ᵈ_ : (B →[ e ] C) → (A →[ d ] B) → (A →[ e + d ] C)
mk g↓ ∘ᵈ mk f↓ = mk (g↓ ∘↓ f↓)

-- Parallel composition
infixr 7 _⊗ᵈ_
_⊗ᵈ_ : (A →[ d ] C) → (B →[ e ] D) → (A × B →[ d ⊓ e ] C × D)
mk f↓ ⊗ᵈ mk g↓ = mk (f↓ ⊗↓ g↓)

infix 0 _→⁰_ _→¹_
_→⁰_ _→¹_ : Set → Set → Set
A →⁰ B = A →[ 0 ] B  -- causal
A →¹ B = A →[ 1 ] B  -- contractive

map⁰ : (A → B) → (A →[ 0 ] B)
map⁰ f = mk (map↓ f)

delay¹ : A → A →¹ A
delay¹ a = mk {f = delayˢ a} delay↓

open import Data.Bool

-- A stream function whose fixed point is a toggle flip-flop without enable.
toggle′ : Bool →¹ Bool
toggle′ = map⁰ not ∘ᵈ delay¹ false
