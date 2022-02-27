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
head (zip (s , t)) = head s , head t
tail (zip (s , t)) = zip (tail s , tail t)

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

≡[]-head : s ≡[ suc n ] t → head s ≡ head t
≡[]-head s~t =  s~t 0 (s≤s z≤n)

≡[]-tail : s ≡[ suc n ] t → tail s ≡[ n ] tail t
≡[]-tail s~t i i<n = s~t (suc i) (s≤s i<n)

≡[≤] : m ≤ n → s ≡[ n ] t → s ≡[ m ] t
≡[≤] m≤n s~ₙt i i<m = s~ₙt i (≤-trans i<m m≤n)

-- Variation (unused)
≡[+] : s ≡[ m + n ] t → s ≡[ m ] t
≡[+] s~t = ≡[≤] (m≤m+n _ _) s~t

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
≤-↓ e≤d delayed-d {n} s~t = ≡[≤] (+-monoˡ-≤ n e≤d) (delayed-d s~t)


-- Constant functions never sense their inputs.
const↓ : constant {A = A} (const s)
const↓ _ _ _ = refl

map↓ : ∀ (f : A → B) → causal (map f)
map↓ f {n} {s} {t} s~t i i<n
  rewrite map-! f s i | map-! f t i | s~t i i<n = refl

-- map↓ f {n} {s} {t} s~t i i<n =
--   begin
--     map f s ! i
--   ≡⟨ map-! f s i ⟩
--     f (s ! i)
--   ≡⟨ cong f (s~t i i<n) ⟩
--     f (t ! i)
--   ≡˘⟨ map-! f t i ⟩
--     map f t ! i
--   ∎

delayˢ : A → A →ˢ A
delayˢ = _◃_

delay↓ : ∀ {a : A} → contractive (delayˢ a)
delay↓ s~t  zero       _     = refl
delay↓ s~t (suc i) (s≤s i<n) = s~t i i<n

-- delay↓ {a = a} {suc n} {s} {t} s~t (suc i) (s≤s i<n) =
--   begin
--     delayˢ a s ! suc i
--   ≡⟨⟩
--     s ! i
--   ≡⟨ s~t i i<n ⟩
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
_⊗↓≡_ {fˢ = fˢ} {gˢ = gˢ} f↓ g↓ {n} {s = s} {t} s~t i i<n =
  begin
    (fˢ ⊗ gˢ) s ! i
  ≡⟨⟩
    zip (fˢ (map proj₁ s) , gˢ (map proj₂ s)) ! i
  ≡⟨ zip-! _ i ⟩
    fˢ (map proj₁ s) ! i , gˢ (map proj₂ s) ! i
  ≡⟨ cong₂ _,_ (∘↓-map f↓ proj₁ s~t i i<n)
               (∘↓-map g↓ proj₂ s~t i i<n) ⟩
    fˢ (map proj₁ t) ! i , gˢ (map proj₂ t) ! i
  ≡˘⟨ zip-! _ i ⟩
    zip (fˢ (map proj₁ t) , gˢ (map proj₂ t)) ! i
  ≡⟨⟩
    (fˢ ⊗ gˢ) t ! i
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

mapᵈ : (A → B) → (A →⁰ B)
mapᵈ f = mk (map↓ f)

delayᵈ : A → A →¹ A
delayᵈ a = mk (delay↓ {a = a})

open import Data.Bool hiding (_≤_; _<_)

-- A stream function whose fixed point is a toggle flip-flop without enable.
toggleᵈ′ : Bool →¹ Bool
toggleᵈ′ = mapᵈ not ∘ᵈ delayᵈ false


-- Alternative representation

-- Representation of causal stream functions
record Gen₀ (A B : Set) : Set where
  coinductive
  constructor mk
  field
    cont : A → B × Gen₀ A B

open Gen₀

gen₀ : Gen₀ A B → A →ˢ B
head (gen₀ g s) = proj₁ (cont g (head s))
tail (gen₀ g s) = gen₀ (proj₂ (cont g (head s))) (tail s)

gen₀↓ : ∀ {g : Gen₀ A B} → gen₀ g ↓ 0
gen₀↓ s~t zero (s≤s _) rewrite ≡[]-head s~t = refl
gen₀↓ {g = g} {t = t} s~t (suc i) (s≤s i<n)
 rewrite ≡[]-head s~t
       | gen₀↓ {g = proj₂ (cont g (head t))} (≡[]-tail s~t) i i<n = refl

-- gen₀↓ {g = g} {s = s} {t} s~t zero (s≤s _) =
--   begin
--     gen₀ g s ! zero
--   ≡⟨⟩
--     proj₁ (cont g (head s))
--   ≡⟨ cong (proj₁ ∘ cont g) (≡[]-head s~t) ⟩
--     proj₁ (cont g (head t))
--   ≡⟨⟩
--     gen₀ g t ! zero
--   ∎

-- gen₀↓ {g = g} {s = s} {t} s~t (suc i) (s≤s i<n) =
--   begin
--     gen₀ g s ! suc i
--   ≡⟨⟩
--     gen₀ (proj₂ (cont g (head s))) (tail s) ! i
--   ≡⟨ cong (λ ● → gen₀ (proj₂ (cont g ●)) (tail s) ! i) (≡[]-head s~t) ⟩
--     gen₀ (proj₂ (cont g (head t))) (tail s) ! i
--   ≡⟨ gen₀↓ {g = proj₂ (cont g (head t))} (≡[]-tail s~t) i i<n ⟩
--     gen₀ (proj₂ (cont g (head t))) (tail t) ! i
--   ≡⟨⟩
--     gen₀ g t ! suc i
--   ∎

-- gen₀ yields causal functions
gen₀ᵈ : Gen₀ A B → A →⁰ B
gen₀ᵈ g = mk (gen₀↓ {g = g})

-- Generating trees parametrized by lag
Gen : ℕ → Set → Set → Set
Gen zero = Gen₀
Gen (suc n) A B = B × Gen n A B

infixr 5 _◂_
_◂_ : B → (A →ˢ B) → (A →ˢ B)
(b ◂ f) s = b ◃ f s

◂-↓ : {b : B} → fˢ ↓ d → (b ◂ fˢ) ↓ suc d
◂-↓ f↓ s~t zero 0<1+d+n = refl
◂-↓ f↓ s~t (suc i) (s≤s i<d+n) = f↓ s~t i i<d+n

-- _◂↓_ {f = f} b f↓ {s = s} {t} s~t (suc i) (s≤s i<d+n) =
--   begin
--     (b ◂ f) s ! suc i
--   ≡⟨⟩
--     f s ! i
--   ≡⟨ f↓ s~t i i<d+n ⟩
--     f t ! i
--   ≡⟨⟩
--     (b ◂ f) t ! suc i
--   ∎

-- _◂↓_ {f = f} b f↓ {s = s} {t} s~t i i<1+d+n =
--   begin
--     (b ◂ f) s ! i
--   ≡⟨ {!!} ⟩
--     {!!}
--   ≡⟨⟩
--     (b ◂ f) t ! i
--   ∎

gen : Gen n A B → A →ˢ B
gen {zero } = gen₀
gen {suc n} (b , gₙ) = b ◂ gen gₙ

gen↓ : ∀ {g : Gen n A B} → gen g ↓ n
gen↓ {n = zero } = gen₀↓
gen↓ {n = suc n} = ◂-↓ gen↓

genᵈ : ∀ (g : Gen n A B) → A →[ n ] B
genᵈ g = mk (gen↓ {g = g})



-- Coalgebraic representation of causal stream functions
record Coalg₀ (A B C : Set) : Set₁ where
  coinductive
  constructor mk
  field
    -- cont : A × C → B × C
    out  : A → C → B
    next : A → C → C

open Coalg₀ public

coalg₀ : Coalg₀ A B C → C → A →ˢ B
head (coalg₀ co c s) = out co (head s) c
tail (coalg₀ co c s) = coalg₀ co (next co (head s) c) (tail s)

-- TODO: Maybe move C into the structure (existentially quantified). I'll then
-- have to move the start state into the record. Probably necessary for a
-- category, since the state type changes.

Coalg : ℕ → Set → Set → Set → Set₁
Coalg zero = Coalg₀
Coalg (suc n) A B C = B × Coalg n A B C

-- Hm. If I map Coalg n to Gen n (as in the paper), I won't have to prove
-- anything else. On the other hand, if I prove the coalgebra version first, the
-- Gen may follow simply by specialization.

coalg₀↓ : ∀ {h : Coalg₀ A B C} {c : C} → coalg₀ h c ↓ 0
coalg₀↓ s~t zero (s≤s _) rewrite ≡[]-head s~t = refl
coalg₀↓ {h = h} {c} {s = s} {t = t} s~t (suc i) (s≤s i<n)
 rewrite ≡[]-head s~t
       | coalg₀↓ {h = h} {c = next h (head t) c} (≡[]-tail s~t) i i<n = refl

-- coalg₀↓ {h = h} {c} {s = s} {t} s~t zero (s≤s _) =
--   begin
--     coalg₀ h c s ! zero
--   ≡⟨⟩
--     out h (head s) c
--   ≡⟨ cong (λ ● → out h ● c) (≡[]-head s~t) ⟩
--     out h (head t) c
--   ≡⟨⟩
--     coalg₀ h c t ! zero
--   ∎

-- coalg₀↓ {h = h} {c} {s = s} {t = t} s~t (suc i) (s≤s i<n) =
--   begin
--     coalg₀ h c s ! suc i
--   ≡⟨⟩
--     coalg₀ h (next h (head s) c) (tail s) ! i
--   ≡⟨ cong (λ ● → coalg₀ h (next h ● c) (tail s) ! i) (≡[]-head s~t) ⟩
--     coalg₀ h (next h (head t) c) (tail s) ! i
--   ≡⟨ coalg₀↓ (≡[]-tail s~t) i i<n ⟩
--     coalg₀ h (next h (head t) c) (tail t) ! i
--   ≡⟨⟩
--     coalg₀ h c t ! suc i
--   ∎

coalg : Coalg n A B C → C → A →ˢ B
coalg {zero } = coalg₀
coalg {suc n} (b , gₙ) c = b ◂ coalg gₙ c

coalg↓ : ∀ {h : Coalg n A B C} {c} → coalg h c ↓ n
coalg↓ {n = zero } = coalg₀↓
coalg↓ {n = suc n} = ◂-↓ coalg↓

coalgᵈ : ∀ (h : Coalg n A B C) (c : C) → A →[ n ] B
coalgᵈ h c = mk (coalg↓ {h = h} {c}) -- TODO: coalg↓ explicit args?


genCoalg₀ : Gen₀ A B → Coalg₀ A B (Gen₀ A B) × Gen₀ A B
genCoalg₀ g₀ = mk (λ a g → proj₁ (cont g a)) (λ a g → proj₂ (cont g a)) , g₀

-- TODO: Gen₀ & Coalg₀ functions both or neither return pairs.
