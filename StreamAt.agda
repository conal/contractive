{-# OPTIONS --guardedness #-}

-- Define and use ! instead of take. Simpler proofs, and more readily
-- generalized beyond streams to other discrete shapes and to continuous time.

module StreamAt where

open import Function using (_∘_; id; const)
open import Data.Product as × hiding (map; zip)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Vec as v using (Vec; []; _∷_)
open import Data.Vec.Properties

open import Relation.Binary.PropositionalEquality ; open ≡-Reasoning

record Stream A : Set where
  coinductive
  constructor _◃_ 
  field
    head : A
    tail : Stream A

open Stream public

private variable
  A B C D : Set
  m n d e : ℕ
  s t : Stream A
  f g : A → B

infix 8 _!_
_!_ : Stream A → ℕ → A
s ! zero  = head s
s ! suc i = tail s ! i

-- Stream functions
infix 0 _→ˢ_
_→ˢ_ : Set → Set → Set
A →ˢ B = Stream A → Stream B

private variable fˢ gˢ hˢ : A →ˢ B

map : (A → B) → (A →ˢ B)
head (map f s) =     f (head s)
tail (map f s) = map f (tail s)

map-! : ∀ (f : A → B) s i → map f s ! i ≡ f (s ! i)
map-! f s  zero   = refl
map-! f s (suc i) = map-! f (tail s) i

zip : Stream A × Stream B → Stream (A × B)
head (zip (xs , ys)) = head xs , head ys
tail (zip (xs , ys)) = zip (tail xs , tail ys)

zip-! : ∀ ((s , t) : Stream A × Stream B) i → zip (s , t) ! i ≡ (s ! i , t ! i)
zip-! (s , t)  zero  = refl
zip-! (s , t) (suc i) = zip-! (tail s , tail t) i

unzip : Stream (A × B) → Stream A × Stream B
unzip zs = map proj₁ zs , map proj₂ zs

infixr 7 _⊗_
_⊗_ : (A →ˢ C) → (B →ˢ D) → (A × B →ˢ C × D)
f ⊗ g = zip ∘ ×.map f g ∘ unzip

infix 4 _≡[_]_
_≡[_]_ : Stream A → ℕ → Stream A → Set
s ≡[ n ] t = ∀ i → i < n → s ! i ≡ t ! i

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
≤-↓ e≤d delayed-d {n} s∼t = ≡[≤] (+-monoˡ-≤ n e≤d) (delayed-d s∼t)


-- Constant functions never sense their inputs.
const↓ : constant {A = A} (const s)
const↓ _ _ _ = refl

map↓ : ∀ (f : A → B) → causal (map f)
map↓ f {n} {s} {t} s∼t i i<n
  rewrite map-! f s i | map-! f t i | s∼t i i<n = refl

-- map↓ f {n} {s} {t} s∼t i i<n =
--   begin
--     map f s ! i
--   ≡⟨ map-! f s i ⟩
--     f (s ! i)
--   ≡⟨ cong f (s∼t i i<n) ⟩
--     f (t ! i)
--   ≡˘⟨ map-! f t i ⟩
--     map f t ! i
--   ∎

delayˢ : A → A →ˢ A
delayˢ = _◃_

delay↓ : ∀ {a : A} → contractive (delayˢ a)
delay↓ s∼t  zero       _     = refl
delay↓ s∼t (suc i) (s≤s i<n) = s∼t i i<n

-- delay↓ {a = a} {suc n} {s} {t} s∼t (suc i) (s≤s i<n) =
--   begin
--     delayˢ a s ! suc i
--   ≡⟨⟩
--     s ! i
--   ≡⟨ s∼t i i<n ⟩
--     t ! i
--   ≡⟨⟩
--     delayˢ a t ! suc i
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
_⊗↓≡_ {fˢ = fˢ} {gˢ = gˢ} f↓ g↓ {n} {s = s} {t} s∼t i i<n =
  begin
    (fˢ ⊗ gˢ) s ! i
  ≡⟨⟩
    zip (fˢ (map proj₁ s) , gˢ (map proj₂ s)) ! i
  ≡⟨ zip-! _ i ⟩
    fˢ (map proj₁ s) ! i , gˢ (map proj₂ s) ! i
  ≡⟨ cong₂ _,_ (∘↓-map f↓ proj₁ s∼t i i<n)
               (∘↓-map g↓ proj₂ s∼t i i<n) ⟩
    fˢ (map proj₁ t) ! i , gˢ (map proj₂ t) ! i
  ≡˘⟨ zip-! _ i ⟩
    zip (fˢ (map proj₁ t) , gˢ (map proj₂ t)) ! i
  ≡⟨⟩
    (fˢ ⊗ gˢ) t ! i
  ∎

-- Parallel composition with arbitrary delays
delayed-⊗ : fˢ ↓ d → gˢ ↓ e → fˢ ⊗ gˢ ↓ d ⊓ e
delayed-⊗ f↓ g↓ = ≤-↓ (m⊓n≤m _ _) f↓ ⊗↓≡ ≤-↓ (m⊓n≤n _ _) g↓

-- TODO: Try defining delayed-⊗ directly rather than via ⊗↓≡ .

-- Stream functions delayed by d
infix 0 _→[_]_
_→[_]_ : Set → ℕ → Set → Set
A →[ d ] B = Σ (A →ˢ B) (_↓ d)

-- Sequential composition
infixr 9 _∘ᵈ_
_∘ᵈ_ : (B →[ e ] C) → (A →[ d ] B) → (A →[ e + d ] C)
(g , g↓) ∘ᵈ (f , f↓) = g ∘ f , g↓ ∘↓ f↓

-- Parallel composition
infixr 7 _⊗ᵈ_
_⊗ᵈ_ : (A →[ d ] C) → (B →[ e ] D) → (A × B →[ d ⊓ e ] C × D)
(f , f↓) ⊗ᵈ (g , g↓) = f ⊗ g , delayed-⊗ f↓ g↓

infix 0 _→⁰_ _→¹_
_→⁰_ _→¹_ : Set → Set → Set
A →⁰ B = A →[ 0 ] B  -- causal
A →¹ B = A →[ 1 ] B  -- contractive

map⁰ : (A → B) → (A →[ 0 ] B)
map⁰ f = map f , map↓ f

delay¹ : A → A →¹ A
delay¹ a = delayˢ a , delay↓

open import Data.Bool

-- A stream function whose fixed point is a toggle flip-flop without enable.
toggle′ : Bool →¹ Bool
toggle′ = map⁰ not ∘ᵈ delay¹ false
