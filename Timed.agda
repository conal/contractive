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
f ⊗ g = f ∘ exl ▵ g ∘ exr

-- f ⊗ g = zip ∘ ×.map f g ∘ unzip


Retime : (h : Time → Time) → Obj → Obj
Retime h (obj ts) = obj (h ∘ ts)

DelayBy : Time → Obj → Obj
DelayBy d = Retime (d +_)

Delay : Obj → Obj
Delay = DelayBy 1

retimeᵗ : (h : Time → Time) → A →ᵗ Retime h A
retimeᵗ _ (vals at) = vals at

delayByᵗ : (d : Time) → A →ᵗ DelayBy d A
delayByᵗ Δt = retimeᵗ (Δt +_)

delayᵗ : A →ᵗ Delay A
delayᵗ = delayByᵗ 1

-- A guess. Useful?
Retime₂ : (_⊕_ : Time → Time → Time) → Obj → Obj → Obj
Retime₂ _⊕_ (obj {I} s) (obj {J} t) = obj {I × J} (λ (i , j) → s i ⊕ t j)


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
constant f = ∀ {d} → f ↓ d

private variable d e : Time

≤-↓ : e ≤ d → fᵗ ↓ d → fᵗ ↓ e
≤-↓ e≤d ↓d {n} s~t = ≡[≤] (+-monoˡ-≤ n e≤d) (↓d s~t)

≡-↓ : d ≡ e → fᵗ ↓ d → fᵗ ↓ e
≡-↓ refl = id

≡-+0-↓ : fᵗ ↓ (d + 0) → fᵗ ↓ d
≡-+0-↓ {d = d} = ≡-↓ (+-identityʳ d)

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

-- TODO: Working on reindex↓. Meanwhile, two easily proved specializations: 

reindex↓-inj₁ : causal (reindex {A ×̇ B} {A} inj₁)
reindex↓-inj₁ u~v = u~v ∘ inj₁

reindex↓-inj₂ : causal (reindex {A ×̇ B} {B} inj₂)
reindex↓-inj₂ u~v = u~v ∘ inj₂

exl↓ : causal (exl {A} {B})
exl↓ = reindex↓-inj₁

exr↓ : causal (exr {A} {B})
exr↓ = reindex↓-inj₂

dup↓ : causal (dup {A})
dup↓ = id↓ ▵↓ id↓

module _ {d e} where

  infixr 7 _⊗↓_
  _⊗↓_ : fᵗ ↓ d → gᵗ ↓ e → (fᵗ ⊗ gᵗ) ↓ (d ⊓ e)
  f↓ ⊗↓ g↓ = ≡-+0-↓ (f↓ ∘↓ exl↓) ▵↓ ≡-+0-↓ (g↓ ∘↓ exr↓)

bump-is-causal : ∀ f → causal (bump {A} f)
bump-is-causal f {n} {s} {t} s~t i i<n rewrite s~t i i<n = refl

∘↓-bump : gᵗ ↓ e → ∀ f → (gᵗ ∘ bump f) ↓ e
∘↓-bump {e = e} g↓ f = ≡-↓ (+-identityʳ e) (g↓ ∘↓ bump-is-causal f)

delayBy-↓ : delayByᵗ {A} d ↓ d
delayBy-↓ {d = d} u~ₑv i d+t<d+e = u~ₑv i (+-cancelˡ-< d d+t<d+e)

-- delayBy-↓ {d = d} {u = u} {v} u~ₑv i d+t<d+e =
--   begin
--     delayByᵗ d u ! i
--   ≡⟨⟩
--     u ! i
--   ≡⟨ u~ₑv i (+-cancelˡ-< d d+t<d+e) ⟩
--     v ! i
--   ≡⟨⟩
--     delayByᵗ d v ! i
--   ∎

delay-is-contractive : contractive (delayᵗ {A})
delay-is-contractive = delayBy-↓

const-is-constant : ∀ {y} → constant {A} {B} (const y)
const-is-constant _ _ _ = refl

-- Functions delayed by d
infix 0 _→[_]_
_→[_]_ : Obj → ℕ → Obj → Set
A →[ d ] B = Σ (A →ᵗ B) (_↓ d)

infix 0 _→⁰_ _→¹_
_→⁰_ _→¹_ : Obj → Obj → Set
A →⁰ B = A →[ 0 ] B  -- causal
A →¹ B = A →[ 1 ] B  -- contractive

-- Delayed functions form an indexed cartesian category.
module IndexedCategory where

  idᵈ : A →⁰ A
  idᵈ = id , id↓

  -- Sequential composition
  infixr 9 _∘̂_
  _∘̂_ : (B →[ e ] C) → (A →[ d ] B) → (A →[ e + d ] C)
  (g , g↓) ∘̂ (f , f↓) = g ∘ f , g↓ ∘↓ f↓

  -- Parallel composition
  infixr 7 _⊗̂_
  _⊗̂_ : (A →[ d ] C) → (B →[ e ] D) → (A ×̇ B →[ d ⊓ e ] C ×̇ D)
  (f , f↓) ⊗̂ (g , g↓) = f ⊗ g , f↓ ⊗↓ g↓

  bumpᵈ : (Atom → Atom) → (A →⁰ A)
  bumpᵈ f = bump f , bump-is-causal f

  delayByᵈ : (d : Time) → A →[ d ] DelayBy d A
  delayByᵈ d = delayByᵗ d , delayBy-↓

  delayᵈ : A →¹ Delay A
  delayᵈ = delayByᵈ 1
  -- delayᵈ = delayᵗ , delay-is-contractive

  bump∘̂delay : (Atom → Atom) → A →¹ Delay A
  bump∘̂delay f = bumpᵈ f ∘̂ delayᵈ

  -- -- Or let Agda fill in the composite delays
  -- bump∘delay′ : (Atom → Atom) → A →[ ? ] DelayBy ? A
  -- bump∘delay′ f = bumpᵈ f ∘̂ delayᵈ

  -- bump∘delay′ : (Atom → Atom) → A →[ _ ] _

  -- -- delay∘bump∘delay : (Atom → Atom) → A →[ {!!} ] DelayBy {!!} A
  -- -- delay∘bump∘delay : (Atom → Atom) → A →[ {!!} ] {!!}
  -- delay∘bump∘delay f = delayᵈ ∘̂ bumpᵈ f ∘̂ delayᵈ

  -- bump⊗̂delay : (Atom → Atom) → A ×̇ B →⁰ A ×̇ Delay B
  bump⊗̂delay : (Atom → Atom) → A ×̇ B →[ zero ] A ×̇ Delay B
  bump⊗̂delay f = bumpᵈ f ⊗̂ delayᵈ

-- Existentially wrapped cartesian category
module Category where

  infix 0 _→ᵈ_
  record _→ᵈ_ (A B : Obj) : Set where
    constructor mk
    field
      {Δ} : Time
      f : A →[ Δ ] B

  module d = IndexedCategory

  idᵈ : A →ᵈ A
  idᵈ = mk d.idᵈ

  infixr 9 _∘̂_
  _∘̂_ : (B →ᵈ C) → (A →ᵈ B) → (A →ᵈ C)
  mk g ∘̂ mk f = mk (g d.∘̂ f)

  infixr 7 _⊗̂_
  _⊗̂_ : (A →ᵈ C) → (B →ᵈ D) → (A ×̇ B →ᵈ C ×̇ D)
  mk f ⊗̂ mk g = mk (f d.⊗̂ g)

  bumpᵈ : (Atom → Atom) → (A →ᵈ A)
  bumpᵈ f = mk (d.bumpᵈ f)

  delayᵈ : A →ᵈ Delay A
  delayᵈ = mk d.delayᵈ

  delayByᵈ : (d : Time) → A →ᵈ DelayBy d A
  delayByᵈ d = mk (d.delayByᵈ d)

  bump∘̂delay : (Atom → Atom) → A →ᵈ Delay A
  bump∘̂delay f = mk (d.bump∘̂delay f)
