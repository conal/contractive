-- Timed functions and generalized contractivity
module Timed (Atom : Set) where

open import Function using (id; const) renaming (_∘_ to _∘_)
open import Data.Product as × hiding (zip)
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

-- Transform all atoms uniformly
bump : (Atom → Atom) → A →ᵗ A
bump f (vals at) = vals (f ∘ at)

-- We'll probably have more sophisticated forms of mapping, in which we
-- transform clusters of bits, e.g., number representations. Think of as indexed
-- by a pair.

zip : Values A × Values B → Values (A ×̇ B)
zip (vals f , vals g) = vals [ f , g ]

unzip : Values (A ×̇ B) → Values A × Values B
unzip (vals h) = vals (h ∘ inj₁) , vals (h ∘ inj₂)

reindex : ∀ {A B} → (Index B → Index A) → A →ᵗ B
reindex f (vals h) = vals (h ∘ f)

infixr 7 _▵_
_▵_ : (A →ᵗ C) → (A →ᵗ D) → (A →ᵗ C ×̇ D)
f ▵ g = zip ∘ < f , g >

exl : A ×̇ B →ᵗ A
exl = reindex inj₁

exr : A ×̇ B →ᵗ B
exr = reindex inj₂

-- Then standard dup and ⊗ recipes

dup : A →ᵗ A ×̇ A
dup = id ▵ id

infixr 7 _⊗_
_⊗_ : (A →ᵗ C) → (B →ᵗ D) → (A ×̇ B →ᵗ C ×̇ D)
f ⊗ g = f ∘ exl ▵ g ∘ exr       -- standard cartesian recipe

-- f ⊗ g = zip ∘ ×.map f g ∘ unzip

Retime : (h : Time → Time) → Obj → Obj
Retime h (obj ts) = obj (h ∘ ts)

Delay : Time → Obj → Obj
Delay d = Retime (d +_)

retimeᵗ : (h : Time → Time) → A →ᵗ Retime h A
retimeᵗ _ (vals at) = vals at

-- A guess. Useful?
Retime₂ : (_⊕_ : Time → Time → Time) → Obj → Obj → Obj
Retime₂ _⊕_ (obj {I} s) (obj {J} t) = obj {I × J} (λ (i , j) → s i ⊕ t j)

delayᵗ : {d : Time} → A →ᵗ Delay d A
delayᵗ {d = d} = retimeᵗ (d +_)


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

causal : (A →ᵗ B) → Set
causal f = f ↓ 0

contractive : (A →ᵗ B) → Set
contractive f = f ↓ 1

constant : (A →ᵗ B) → Set
constant f = ∀ {d} → f ↓ d   -- infinite delay

private variable d e : Time

≤-↓ : e ≤ d → fᵗ ↓ d → fᵗ ↓ e
≤-↓ e≤d ↓d s~t = ≡[≤] (+-monoˡ-≤ _ e≤d) (↓d s~t)

≡-↓ : d ≡ e → fᵗ ↓ d → fᵗ ↓ e
≡-↓ refl = id

+0-↓ : fᵗ ↓ (d + 0) → fᵗ ↓ d
+0-↓ = ≡-↓ (+-identityʳ _)

id↓ : causal {A} id
id↓ = id

module _ {d e} where

  infixr 9 _∘↓_
  _∘↓_ : gᵗ ↓ e → fᵗ ↓ d → (gᵗ ∘ fᵗ) ↓ (e + d)
  (g↓ ∘↓ f↓) {n} rewrite +-assoc e d n = g↓ ∘ f↓

  infixr 7 _▵↓_
  _▵↓_ : fᵗ ↓ d → gᵗ ↓ e → (fᵗ ▵ gᵗ) ↓ (d ⊓ e)
  (f↓ ▵↓ g↓) u~v = [ ≤-↓ (m⊓n≤m _ _) f↓ u~v , ≤-↓ (m⊓n≤n _ _) g↓ u~v ]

-- reindex↓ : ∀ f → causal (reindex {A} {B} f)
-- reindex↓ f u~v i d<e = u~v (f i) {!!}

-- Goal: times A (f i) < e
-- d<e : times B i < e

-- TODO: Something like reindex↓. Meanwhile, two easily proved specializations: 

reindex↓-inj₁ : causal (reindex {A ×̇ B} {A} inj₁)
reindex↓-inj₁ = _∘ inj₁

reindex↓-inj₂ : causal (reindex {A ×̇ B} {B} inj₂)
reindex↓-inj₂ = _∘ inj₂

exl↓ : causal (exl {A} {B})
exl↓ = reindex↓-inj₁

exr↓ : causal (exr {A} {B})
exr↓ = reindex↓-inj₂

dup↓ : causal (dup {A})
dup↓ = id↓ ▵↓ id↓

infixr 7 _⊗↓_
_⊗↓_ : fᵗ ↓ d → gᵗ ↓ e → (fᵗ ⊗ gᵗ) ↓ (d ⊓ e)
f↓ ⊗↓ g↓ = +0-↓ (f↓ ∘↓ exl↓) ▵↓ +0-↓ (g↓ ∘↓ exr↓)

bump-is-causal : ∀ f → causal (bump {A} f)
bump-is-causal f {s} {t} s~t i i<n rewrite s~t i i<n = refl

∘↓-bump : gᵗ ↓ e → ∀ f → (gᵗ ∘ bump f) ↓ e
∘↓-bump {e = e} g↓ f = ≡-↓ (+-identityʳ e) (g↓ ∘↓ bump-is-causal f)

delay-↓ : delayᵗ {A} ↓ d
delay-↓ {d = d} u~ₑv i d+t<d+e = u~ₑv i (+-cancelˡ-< d d+t<d+e)

-- delay-↓ {d = d} {u = u} {v} u~ₑv i d+t<d+e =
--   begin
--     delayᵗ d u ! i
--   ≡⟨⟩
--     u ! i
--   ≡⟨ u~ₑv i (+-cancelˡ-< d d+t<d+e) ⟩
--     v ! i
--   ≡⟨⟩
--     delayᵗ d v ! i
--   ∎

const-is-constant : ∀ {y} → constant {A} {B} (const y)
const-is-constant _ _ _ = refl

-- Delayed functions
infix 0 _→ᵈ_
record _→ᵈ_ (A B : Obj) : Set where
  constructor Δ
  field
    {f} : A →ᵗ B
    {δ} : Time
    f↓ : f ↓ δ

-- Delayed functions form a cartesian category.

idᵈ : A →ᵈ A
idᵈ = Δ id↓

-- Sequential composition
infixr 9 _∘̂_
_∘̂_ : (B →ᵈ C) → (A →ᵈ B) → (A →ᵈ C)
Δ g↓ ∘̂ Δ f↓ = Δ (g↓ ∘↓ f↓)

-- Parallel composition
infixr 7 _⊗̂_
_⊗̂_ : (A →ᵈ C) → (B →ᵈ D) → (A ×̇ B →ᵈ C ×̇ D)
Δ f↓ ⊗̂ Δ g↓ = Δ (f↓ ⊗↓ g↓)

bumpᵈ : (Atom → Atom) → (A →ᵈ A)
bumpᵈ f = Δ (bump-is-causal f)

delayᵈ : A →ᵈ Delay d A
delayᵈ = Δ delay-↓

bump∘̂delay : (Atom → Atom) → A →ᵈ Delay d A
bump∘̂delay f = bumpᵈ f ∘̂ delayᵈ

bump⊗̂delay : (Atom → Atom) → A ×̇ B →ᵈ A ×̇ Delay d B
bump⊗̂delay f = bumpᵈ f ⊗̂ delayᵈ
