{-# OPTIONS --guardedness #-}

-- Infinite k-ary trees, where k is a type (not number). Generalizes streams and
-- binary trees.

module TreeFun (I : Set) where

open import Function using (id; const) renaming (_∘′_ to _∘_)
open import Data.Product as × hiding (map; zip)
open import Data.List as L hiding (map; zip; unzip)
open import Data.Nat
open import Data.Nat.Properties

open import Relation.Binary.PropositionalEquality ; open ≡-Reasoning

Tree : Set → Set
Tree A = List I → A

private variable
  A B C D : Set
  m n d e : ℕ
  s t : Tree A
  f g : A → B

-- Tree functions
infix 0 _→ᵗ_
_→ᵗ_ : Set → Set → Set
A →ᵗ B = Tree A → Tree B

private variable fᵗ gᵗ hᵗ : A →ᵗ B

map : (A → B) → (A →ᵗ B)
map = _∘_
-- map f s = f ∘ s

zip : Tree A × Tree B → Tree (A × B)
zip = uncurry <_,_>
-- zip (s , t) i = s i , t i

unzip : Tree (A × B) → Tree A × Tree B
unzip zs = map proj₁ zs , map proj₂ zs

infixr 7 _⊗_
_⊗_ : (A →ᵗ C) → (B →ᵗ D) → (A × B →ᵗ C × D)
f ⊗ g = zip ∘ ×.map f g ∘ unzip

delayᵗ : A → A →ᵗ A
delayᵗ a s   []     = a
delayᵗ a s (i ∷ is) = s is

infix 4 _≡[_]_
_≡[_]_ : Tree A → ℕ → Tree A → Set
s ≡[ n ] t = ∀ i → length i < n → s i ≡ t i

≡[≤] : m ≤ n → s ≡[ n ] t → s ≡[ m ] t
≡[≤] m≤n s∼ₙt i i<m = s∼ₙt i (≤-trans i<m m≤n)

-- Variation (unused)
≡[+] : s ≡[ m + n ] t → s ≡[ m ] t
≡[+] s∼t = ≡[≤] (m≤m+n _ _) s∼t

-- Input influence is delayed by at least d steps.
infix 4 _↓_
_↓_ : (A →ᵗ B) → ℕ → Set
f ↓ d = ∀ {n s t} → s ≡[ n ] t → f s ≡[ d + n ] f t

causal : (A →ᵗ B) → Set
causal f = f ↓ 0

contractive : (A →ᵗ B) → Set
contractive f = f ↓ 1

constant : (A →ᵗ B) → Set
constant f = ∀ {d} → f ↓ d

≤-↓ : e ≤ d → fᵗ ↓ d → fᵗ ↓ e
≤-↓ e≤d ↓d {n} s∼t = ≡[≤] (+-monoˡ-≤ n e≤d) (↓d s∼t)

≡-↓ : d ≡ e → fᵗ ↓ d → fᵗ ↓ e
≡-↓ refl = id

-- ≡-↓ d≡e = ≤-↓ (≤-reflexive (sym d≡e))

map-is-causal : ∀ (f : A → B) → causal (map f)
map-is-causal f {n} {s} {t} s∼t i i<n rewrite s∼t i i<n = refl

delay-is-contractive : ∀ {a : A} → contractive (delayᵗ a)
delay-is-contractive s∼t   []         _     = refl
delay-is-contractive s∼t (i ∷ is) (s≤s i<n) = s∼t is i<n

const-is-constant : constant {A = A} (const s)
const-is-constant _ _ _ = refl

-- Sequential composition adds delays.
infixr 9 _∘↓_
_∘↓_ : gᵗ ↓ e → fᵗ ↓ d → (gᵗ ∘ fᵗ) ↓ (e + d)
_∘↓_ {e = e} {d = d} g↓ f↓ {n} rewrite +-assoc e d n = g↓ ∘ f↓

∘↓-map : gᵗ ↓ e → (f : A → B) → (gᵗ ∘ map f) ↓ e
∘↓-map {e = e} g↓ f = ≡-↓ (+-identityʳ e) (g↓ ∘↓ map-is-causal f)

-- Parallel composition with equal delays
infixr 7 _⊗↓≡_
_⊗↓≡_ : fᵗ ↓ d → gᵗ ↓ d → (fᵗ ⊗ gᵗ) ↓ d
_⊗↓≡_ {fᵗ = fᵗ} {gᵗ = gᵗ} f↓ g↓ {n} {s = s} {t} s∼t i i<n =
  begin
    (fᵗ ⊗ gᵗ) s i
  ≡⟨⟩
    fᵗ (map proj₁ s) i , gᵗ (map proj₂ s) i
  ≡⟨ cong₂ _,_ (∘↓-map f↓ proj₁ s∼t i i<n) (∘↓-map g↓ proj₂ s∼t i i<n) ⟩
    fᵗ (map proj₁ t) i , gᵗ (map proj₂ t) i
  ≡⟨⟩
    (fᵗ ⊗ gᵗ) t i
  ∎

-- Parallel composition with arbitrary delays
infixr 7 _⊗↓_
_⊗↓_ : fᵗ ↓ d → gᵗ ↓ e → (fᵗ ⊗ gᵗ) ↓ (d ⊓ e)
f↓ ⊗↓ g↓ = ≤-↓ (m⊓n≤m _ _) f↓ ⊗↓≡ ≤-↓ (m⊓n≤n _ _) g↓

-- Stream functions delayed by d
infix 0 _→[_]_
_→[_]_ : Set → ℕ → Set → Set
A →[ d ] B = Σ (A →ᵗ B) (_↓ d)

infix 0 _→⁰_ _→¹_
_→⁰_ _→¹_ : Set → Set → Set
A →⁰ B = A →[ 0 ] B  -- causal
A →¹ B = A →[ 1 ] B  -- contractive

-- Sequential composition
infixr 9 _∘̂_
_∘̂_ : (B →[ e ] C) → (A →[ d ] B) → (A →[ e + d ] C)
(g , g↓) ∘̂ (f , f↓) = g ∘ f , g↓ ∘↓ f↓

-- Parallel composition
infixr 7 _⊗̂_
_⊗̂_ : (A →[ d ] C) → (B →[ e ] D) → (A × B →[ d ⊓ e ] C × D)
(f , f↓) ⊗̂ (g , g↓) = f ⊗ g , f↓ ⊗↓ g↓

map⁰ : (A → B) → (A →⁰ B)
map⁰ f = map f , map-is-causal f

delay¹ : A → (A →¹ A)
delay¹ a = delayᵗ a , delay-is-contractive
