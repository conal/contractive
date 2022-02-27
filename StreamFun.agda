-- This version formulates "streams" directly as functions.
{-# OPTIONS --guardedness #-}  -- for Gen₀

module StreamFun where

open import Function using (_∘_; id; const)
open import Data.Product as × hiding (map; zip)
open import Data.Nat
open import Data.Nat.Properties

open import Relation.Binary.PropositionalEquality ; open ≡-Reasoning

Stream : Set → Set
Stream A = ℕ → A

private variable
  A B C D : Set
  m n d e : ℕ
  s t : Stream A

infixr 5 _∷_
_∷_ : A → Stream A → Stream A
(x ∷ xs)  zero   = x
(x ∷ xs) (suc i) = xs i

head : Stream A → A
head xs = xs zero

tail : Stream A → Stream A
tail xs = xs ∘ suc


-- Stream functions
infix 0 _→ˢ_
_→ˢ_ : Set → Set → Set
A →ˢ B = Stream A → Stream B

private variable fˢ gˢ hˢ : A →ˢ B

map : (A → B) → (A →ˢ B)
map f s = f ∘ s

zip : Stream A × Stream B → Stream (A × B)
zip = uncurry <_,_>
-- zip (s , t) i = s i , t i

unzip : Stream (A × B) → Stream A × Stream B
unzip zs = map proj₁ zs , map proj₂ zs

infixr 7 _⊗_
_⊗_ : (A →ˢ C) → (B →ˢ D) → (A × B →ˢ C × D)
f ⊗ g = zip ∘ ×.map f g ∘ unzip

delayˢ : A → A →ˢ A
delayˢ a s  zero   = a
delayˢ a s (suc i) = s i

infix 4 _≡[_]_
_≡[_]_ : Stream A → ℕ → Stream A → Set
s ≡[ n ] t = ∀ i → i < n → s i ≡ t i

≡[≤] : m ≤ n → s ≡[ n ] t → s ≡[ m ] t
≡[≤] m≤n s∼ₙt i i<m = s∼ₙt i (≤-trans i<m m≤n)

-- Variation (unused)
≡[+] : s ≡[ m + n ] t → s ≡[ m ] t
≡[+] s∼t = ≡[≤] (m≤m+n _ _) s∼t

-- Input influence is delayed by at least d steps.
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
≤-↓ e≤d ↓d {n} s∼t = ≡[≤] (+-monoˡ-≤ n e≤d) (↓d s∼t)


map↓ : ∀ (f : A → B) → causal (map f)
map↓ f {n} {s} {t} s∼t i i<n rewrite s∼t i i<n = refl

delay↓ : ∀ {a : A} → contractive (delayˢ a)
delay↓ s∼t  zero       _     = refl
delay↓ s∼t (suc i) (s≤s i<n) = s∼t i i<n

const↓ : constant {A = A} (const s)
const↓ _ _ _ = refl

-- Sequential composition adds delays.
infixr 9 _∘↓_
_∘↓_ : gˢ ↓ e → fˢ ↓ d → (gˢ ∘ fˢ) ↓ (e + d)
_∘↓_ {e = e} {d = d} g↓ f↓ {n} rewrite +-assoc e d n = g↓ ∘ f↓

∘↓-map : gˢ ↓ e → (f : A → B) → (gˢ ∘ map f) ↓ e
∘↓-map {e = e} g↓ f = ≡-↓ (+-identityʳ e) (g↓ ∘↓ map↓ f)

-- Parallel composition with equal delays
infixr 7 _⊗↓≡_
_⊗↓≡_ : fˢ ↓ d → gˢ ↓ d → (fˢ ⊗ gˢ) ↓ d
_⊗↓≡_ {fˢ = fˢ} {gˢ = gˢ} f↓ g↓ {n} {s = s} {t} s∼t i i<n =
  begin
    (fˢ ⊗ gˢ) s i
  ≡⟨⟩
    fˢ (map proj₁ s) i , gˢ (map proj₂ s) i
  ≡⟨ cong₂ _,_ (∘↓-map f↓ proj₁ s∼t i i<n) (∘↓-map g↓ proj₂ s∼t i i<n) ⟩
    fˢ (map proj₁ t) i , gˢ (map proj₂ t) i
  ≡⟨⟩
    (fˢ ⊗ gˢ) t i
  ∎

-- Parallel composition with arbitrary delays
infixr 7 _⊗↓_
_⊗↓_ : fˢ ↓ d → gˢ ↓ e → (fˢ ⊗ gˢ) ↓ (d ⊓ e)
f↓ ⊗↓ g↓ = ≤-↓ (m⊓n≤m _ _) f↓ ⊗↓≡ ≤-↓ (m⊓n≤n _ _) g↓

-- TODO: Try defining ⊗↓ directly rather than via ⊗↓-≡ .

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

map⁰ : (A → B) → (A →⁰ B)
map⁰ f = mk (map↓ f)

delay¹ : A → A →¹ A
delay¹ a = mk (delay↓ {a = a})

open import Data.Bool

-- A stream function whose fixed point is a toggle flip-flop without enable.
toggle′ : Bool →¹ Bool
toggle′ = map⁰ not ∘ᵈ delay¹ false
