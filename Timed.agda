-- Timed functions and generalized contractivity
module Timed (Atom : Set) where

open import Function using (id; const) renaming (_∘_ to _∘_)
open import Data.Product as × hiding (map; zip)
  renaming (map₁ to first; map₂ to second)
-- open import Data.List as L hiding (map; zip; unzip)
open import Data.Nat
open import Data.Nat.Properties

open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning

-- Time. ℕ for now.
Time : Set
Time = ℕ

-- TODO: generalize from ℕ to any well-founded partial order. See
-- Induction.WellFounded in agda-stdlib.

record Obj : Set₁ where
  constructor obj
  field
    {Index} : Set
    times : Index → Time

open Obj public

-- or ∃ λ i → I → Atom

open import Data.Empty
open import Data.Sum

⊤̇ : Obj
⊤̇ = obj {⊥} λ ()

infixr 4 _×̇_
_×̇_ : Obj → Obj → Obj
obj s ×̇ obj t = obj [ s , t ]

-- obj {I} s ×̇ obj {J} t = obj {I ⊎ J} [ s , t ]

-- Wrapper to help with time inference
record Values (A : Obj) : Set where
  constructor vals
  infix 9 _!_
  field
    _!_ : Index A → Atom

open Values public

-- Timed functions
infix 0 _→ᵗ_
_→ᵗ_ : Obj → Obj → Set
A →ᵗ B = Values A → Values B

private variable
  I J : Set
  A B C D : Obj
  s t : Time
  u v : Values A
  fᵗ gᵗ hᵗ : A →ᵗ B

-- map : (A → B) → (A →ᵗ B)
-- map = _∘_
-- -- map f s = f ∘ s

zip : Values A × Values B → Values (A ×̇ B)
zip (vals f , vals g) = vals [ f , g ]

unzip : Values (A ×̇ B) → Values A × Values B
unzip (vals h) = vals (h ∘ inj₁) , vals (h ∘ inj₂)

infixr 7 _⊗_
_⊗_ : (A →ᵗ C) → (B →ᵗ D) → (A ×̇ B →ᵗ C ×̇ D)
f ⊗ g = zip ∘ ×.map f g ∘ unzip


Retime : (h : Time → Time) → Obj → Obj
Retime h (obj ts) = obj (h ∘ ts)

DelayBy : Time → Obj → Obj
DelayBy d = Retime (d +_)

Delay : Obj → Obj
Delay = DelayBy 1

retimeᵗ : (h : Time → Time) → A →ᵗ Retime h A
retimeᵗ h (vals at) = vals at

delayByᵗ : (d : Time) → A →ᵗ DelayBy d A
delayByᵗ Δt = retimeᵗ (Δt +_)

delayᵗ : A →ᵗ Delay A
delayᵗ = delayByᵗ 1

module A where

  module _ {A@(obj {I} ts) : Obj} where

    infix 4 _≡[_]_
    _≡[_]_ : Values A → Time → Values A → Set
    u ≡[ t ] v = ∀ (i : I) → ts i < t → u ! i ≡ v ! i

  ≡[≤] : s ≤ t → u ≡[ t ] v → u ≡[ s ] v
  ≡[≤] s≤t u~ₜv i i<s = u~ₜv i (≤-trans i<s s≤t)

  -- Input influence is delayed by at least d steps.
  infix 4 _↓_
  _↓_ : (A →ᵗ B) → Time → Set
  f ↓ d = ∀ {e u v} → u ≡[ e ] v → f u ≡[ d + e ] f v

-- Generalize to a t per index
module B where

  module _ {A@(obj {I} ts) : Obj} where

    infix 4 _≡[_]_
    _≡[_]_ : Values A → (I → Time) → Values A → Set
    u ≡[ t ] v = ∀ (i : I) → ts i < t i → u ! i ≡ v ! i

  private variable Δs Δt : I → Time

  ≡[≤] : (∀ i → Δs i ≤ Δt i) → u ≡[ Δt ] v → u ≡[ Δs ] v
  ≡[≤] s≤t u~ₜv i i<s = u~ₜv i (≤-trans i<s (s≤t i))

  -- I don't know how to generalize `_↓_` accordingly, considering that the
  -- domain and codomain can have different shapes (index types).

open A

causal : (A →ᵗ B) → Set
causal f = f ↓ 0

contractive : (A →ᵗ B) → Set
contractive f = f ↓ 1

constant : (A →ᵗ B) → Set
constant f = ∀ {d} → f ↓ d

private variable d e : Time

≤-↓ : e ≤ d → fᵗ ↓ d → fᵗ ↓ e
≤-↓ e≤d ↓d {n} s~t = ≡[≤] (+-monoˡ-≤ n e≤d) (↓d s~t)

≡-↓ : d ≡ e → fᵗ ↓ d → fᵗ ↓ e
≡-↓ refl = id

-- map-is-causal : ∀ (f : A → B) → causal (map f)
-- map-is-causal f {n} {s} {t} s~t i i<n rewrite s~t i i<n = refl

delay-is-contractive : contractive (delayᵗ {A})
delay-is-contractive u~ₑv j (s≤s sd≤e) = u~ₑv j sd≤e

const-is-constant : ∀ {y} → constant {A} {B} (const y)
const-is-constant _ _ _ = refl

-- ∘↓-map : gᵗ ↓ e → (f : A → B) → (gᵗ ∘ map f) ↓ e
-- ∘↓-map {e = e} g↓ f = ≡-↓ (+-identityʳ e) (g↓ ∘↓ map-is-causal f)

-- Sequential composition adds delays.
infixr 9 _∘↓_
_∘↓_ : gᵗ ↓ e → fᵗ ↓ d → (gᵗ ∘ fᵗ) ↓ (e + d)
_∘↓_ {e = e} {d = d} g↓ f↓ {n} rewrite +-assoc e d n = g↓ ∘ f↓

-- Parallel composition with arbitrary delays
infixr 7 _⊗↓_
_⊗↓_ : fᵗ ↓ d → gᵗ ↓ e → (fᵗ ⊗ gᵗ) ↓ (d ⊓ e)
(f↓ ⊗↓ g↓) u~v = [ ≤-↓ (m⊓n≤m _ _) f↓ (u~v ∘ inj₁)
                 , ≤-↓ (m⊓n≤n _ _) g↓ (u~v ∘ inj₂) ]

-- Stream functions delayed by d
infix 0 _→[_]_
_→[_]_ : Obj → ℕ → Obj → Set
A →[ d ] B = Σ (A →ᵗ B) (_↓ d)

infix 0 _→⁰_ _→¹_
_→⁰_ _→¹_ : Obj → Obj → Set
A →⁰ B = A →[ 0 ] B  -- causal
A →¹ B = A →[ 1 ] B  -- contractive

-- Sequential composition
infixr 9 _∘̂_
_∘̂_ : (B →[ e ] C) → (A →[ d ] B) → (A →[ e + d ] C)
(g , g↓) ∘̂ (f , f↓) = g ∘ f , g↓ ∘↓ f↓

-- Parallel composition
infixr 7 _⊗̂_
_⊗̂_ : (A →[ d ] C) → (B →[ e ] D) → (A ×̇ B →[ d ⊓ e ] C ×̇ D)
(f , f↓) ⊗̂ (g , g↓) = f ⊗ g , f↓ ⊗↓ g↓

-- map⁰ : (A → B) → (A →⁰ B)
-- map⁰ f = map f , map-is-causal f

delay¹ : A →¹ Delay A
delay¹ = delayᵗ , delay-is-contractive
