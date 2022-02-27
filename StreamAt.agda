-- {-# OPTIONS --show-implicit #-}
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

take : (n : ℕ) → Stream A → Vec A n
take  zero   s = []
take (suc n) s = head s ∷ take n (tail s)

-- Stream functions
infix 0 _→ˢ_
_→ˢ_ : Set → Set → Set
A →ˢ B = Stream A → Stream B

private variable fˢ gˢ hˢ : A →ˢ B

infixr 5 _◂_
_◂_ : B → (A →ˢ B) → (A →ˢ B)
(b ◂ f) s = b ◃ f s

infixr 5 _◂*_
_◂*_ : Vec B n → (A →ˢ B) → (A →ˢ B)
[] ◂* f = f
(b ∷ bs) ◂* f = b ◂ bs ◂* f

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

constᵈ : (s : Stream B) → A →⁰ B
constᵈ s = mk (const↓ {s = s})

mapᵈ : (A → B) → (A →⁰ B)
mapᵈ f = mk (map↓ f)

delayᵈ : A → A →¹ A
delayᵈ a = mk (delay↓ {a = a})

open import Data.Bool hiding (_≤_; _<_)

-- A stream function whose fixed point is a toggle flip-flop without enable.
toggleᵈ′ : Bool →¹ Bool
toggleᵈ′ = mapᵈ not ∘ᵈ delayᵈ false

infixr 5 _◂↓_
_◂↓_ : (b : B) → fˢ ↓ d → (b ◂ fˢ) ↓ suc d
(b ◂↓ f↓) s~t zero 0<1+d+n = refl
(b ◂↓ f↓) s~t (suc i) (s≤s i<d+n) = f↓ s~t i i<d+n

-- _◂-↓_ {f = f} b f↓ {s = s} {t} s~t (suc i) (s≤s i<d+n) =
--   begin
--     (b ◂ f) s ! suc i
--   ≡⟨⟩
--     f s ! i
--   ≡⟨ f↓ s~t i i<d+n ⟩
--     f t ! i
--   ≡⟨⟩
--     (b ◂ f) t ! suc i
--   ∎

-- _◂-↓_ {f = f} b f↓ {s = s} {t} s~t i i<1+d+n =
--   begin
--     (b ◂ f) s ! i
--   ≡⟨ {!!} ⟩
--     {!!}
--   ≡⟨⟩
--     (b ◂ f) t ! i
--   ∎

infixr 5 _◂*↓_
_◂*↓_ : (bs : Vec B e) → fˢ ↓ d → (bs ◂* fˢ) ↓ (e + d)
[] ◂*↓ f↓ = f↓
(b ∷ bs) ◂*↓ f↓ = b ◂↓ bs ◂*↓ f↓


-- Coalgebraic representation of causal stream functions
record Coalg₀ (A B C : Set) : Set₁ where
  coinductive
  constructor mk
  field
    cont : C × A → C × B

open Coalg₀ public

coalg₀ : Coalg₀ A B C → C → A →ˢ B
head (coalg₀ co c s) = proj₂ (cont co (c , head s))
tail (coalg₀ co c s) = coalg₀ co (proj₁ (cont co (c , head s))) (tail s)

coalg₀↓ : ∀ {h : Coalg₀ A B C} {c : C} → causal (coalg₀ h c)
coalg₀↓ s~t zero (s≤s _) rewrite ≡[]-head s~t = refl
coalg₀↓ {h = h} {c} {s = s} {t = t} s~t (suc i) (s≤s i<n)
 rewrite ≡[]-head s~t | coalg₀↓ {h = h} {c = proj₁ (cont h (c , head t))}
                                (≡[]-tail s~t) i i<n   = refl

-- coalg₀↓ {h = h} {c} {s = s} {t} s~t zero (s≤s _) =
--   begin
--     coalg₀ h c s ! zero
--   ≡⟨⟩
--     proj₁ (cont h (head s , c))
--   ≡⟨ cong (λ ● → proj₁ (cont h (● , c))) (≡[]-head s~t) ⟩
--     proj₁ (cont h (c , head t))
--   ≡⟨⟩
--     coalg₀ h c t ! zero
--   ∎

-- coalg₀↓ {h = h} {c} {s = s} {t = t} s~t (suc i) (s≤s i<n) =
--   begin
--     coalg₀ h c s ! suc i
--   ≡⟨⟩
--     coalg₀ h (proj₂ (cont h (head s , c))) (tail s) ! i
--   ≡⟨ cong (λ ● → coalg₀ h (proj₂ (cont h (● , c))) (tail s) ! i) (≡[]-head s~t) ⟩
--     coalg₀ h (proj₂ (cont h (c , head t))) (tail s) ! i
--   ≡⟨ coalg₀↓ (≡[]-tail s~t) i i<n ⟩
--     coalg₀ h (proj₂ (cont h (c , head t))) (tail t) ! i
--   ≡⟨⟩
--     coalg₀ h c t ! suc i
--   ∎

-- Coalgebraic representation of `d`-lagging stream functions
Coalg : ℕ → Set → Set → Set → Set₁
Coalg zero = Coalg₀
Coalg (suc d) A B C = B × Coalg d A B C

coalg : Coalg d A B C → C → A →ˢ B
coalg {zero } = coalg₀
coalg {suc d} (b , gₙ) c = b ◂ coalg gₙ c

coalg↓ : ∀ {h : Coalg d A B C} {c} → coalg h c ↓ d
coalg↓ {d = zero } = coalg₀↓
coalg↓ {d = suc d} = _ ◂↓ coalg↓

coalgᵈ : ∀ (h : Coalg d A B C) (c : C) → A →[ d ] B
coalgᵈ h c = mk (coalg↓ {h = h} {c}) -- TODO: coalg↓ explicit args?

-- Package seed type and value with coalgebra
infix 0 _⇒[_]_
record _⇒[_]_ (A : Set) (d : ℕ) (B : Set) : Set₁ where
  constructor mk
  field
    {S} : Set
    c : S
    h : Coalg d A B S

autᵈ : A ⇒[ d ] B  →  A →[ d ] B
autᵈ (mk h c) = coalgᵈ c h

-- run : {n : ℕ} → Vec A n × (A ⇒[ d ] B) → Vec B n × (A ⇒[ d ] B)
-- run ([] , f) = [] , f
-- run (x ∷ xs , f) = {!!}


{-
TODO:

* _→[_]_ operations on _⇒[_]_
* _→ᵈ_ and _⇒ᵈ_, existentially hiding lags.
* Prove an inverse to `◂-↓`: If `g ↓ suc d`, then `g` can be written as
  `b ◂ f` where `f ↓ d`.
-}

-- -- Sequential composition
-- infixr 9 _∘ᵃ_
-- _∘ᵃ_ : (B ⇒[ e ] C) → (A ⇒[ d ] B) → (A ⇒[ e + d ] C)
-- mk y g ∘ᵃ mk x f = mk (x , y) {!!}

-- -- Parallel composition
-- infixr 7 _⊗ᵃ_
-- _⊗ᵃ_ : (A ⇒[ d ] C) → (B ⇒[ e ] D) → (A × B ⇒[ d ⊓ e ] C × D)
-- mk f↓ ⊗ᵃ mk g↓ = mk (f↓ ⊗↓ g↓)

-- infix 0 _→⁰_ _→¹_
-- _→⁰_ _→¹_ : Set → Set → Set
-- A →⁰ B = A ⇒[ 0 ] B  -- causal
-- A →¹ B = A ⇒[ 1 ] B  -- contractive

-- constᵃ : (s : Stream B) → A →⁰ B
-- constᵃ s = mk (const↓ {s = s})

-- mapᵃ : (A → B) → (A →⁰ B)
-- mapᵃ f = mk (map↓ f)

-- delayᵃ : A → A →¹ A
-- delayᵃ a = mk (delay↓ {a = a})
