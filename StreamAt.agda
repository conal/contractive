-- {-# OPTIONS --show-implicit #-}
{-# OPTIONS --guardedness #-}

-- Define and use ! instead of take. Simpler proofs, and more readily
-- generalized beyond streams to other discrete shapes and to continuous time.

module StreamAt where

open import Function using (_∘_; id; const; _$_)
open import Data.Unit using (⊤; tt)
open import Data.Product as × hiding (map; zip)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Vec as v hiding (head; tail; map; zip; unzip; take)
open import Data.Vec.Properties
open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning

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
  u v : Stream A

infix 8 _!_
_!_ : Stream A → ℕ → A
u ! zero  = head u
u ! suc i = tail u ! i

take : (n : ℕ) → Stream A → Vec A n
take  zero   u = []
take (suc n) u = head u ∷ take n (tail u)

-- Stream functions
infix 0 _→ˢ_
_→ˢ_ : Set → Set → Set
A →ˢ B = Stream A → Stream B

private variable fˢ gˢ hˢ : A →ˢ B

infixr 5 _◂_
_◂_ : B → (A →ˢ B) → (A →ˢ B)
(b ◂ f) u = b ◃ f u

infixr 5 _◂*_
_◂*_ : Vec B n → (A →ˢ B) → (A →ˢ B)
[] ◂* f = f
(b ∷ bs) ◂* f = b ◂ bs ◂* f

map : (A → B) → (A →ˢ B)
head (map f u) =     f (head u)
tail (map f u) = map f (tail u)

map-! : ∀ (f : A → B) u i → map f u ! i ≡ f (u ! i)
map-! f u  zero   = refl
map-! f u (suc i) = map-! f (tail u) i

zip : Stream A × Stream B → Stream (A × B)
head (zip (u , v)) = head u , head v
tail (zip (u , v)) = zip (tail u , tail v)

zip-! : ∀ ((u , v) : Stream A × Stream B) i → zip (u , v) ! i ≡ (u ! i , v ! i)
zip-! (u , v)  zero  = refl
zip-! (u , v) (suc i) = zip-! (tail u , tail v) i

unzip : Stream (A × B) → Stream A × Stream B
unzip zs = map proj₁ zs , map proj₂ zs

infixr 7 _⊗_
_⊗_ : (A →ˢ C) → (B →ˢ D) → (A × B →ˢ C × D)
f ⊗ g = zip ∘ ×.map f g ∘ unzip

infix 4 _≡[_]_
_≡[_]_ : Stream A → ℕ → Stream A → Set
u ≡[ n ] v = ∀ i → i < n → u ! i ≡ v ! i

≡[]-head : u ≡[ suc n ] v → head u ≡ head v
≡[]-head u~v =  u~v 0 (s≤s z≤n)

≡[]-tail : u ≡[ suc n ] v → tail u ≡[ n ] tail v
≡[]-tail u~v i i<n = u~v (suc i) (s≤s i<n)

≡[≤] : m ≤ n → u ≡[ n ] v → u ≡[ m ] v
≡[≤] m≤n s~ₙt i i<m = s~ₙt i (≤-trans i<m m≤n)

-- Variation (unused)
≡[+] : u ≡[ m + n ] v → u ≡[ m ] v
≡[+] u~v = ≡[≤] (m≤m+n _ _) u~v

-- Input influence lags by (at least) d steps.
infix 4 _↓_
_↓_ : (A →ˢ B) → ℕ → Set
f ↓ d = ∀ {n u v} → u ≡[ n ] v → f u ≡[ d + n ] f v

causal : (A →ˢ B) → Set
causal = _↓ 0

contractive : (A →ˢ B) → Set
contractive = _↓ 1

constant : (A →ˢ B) → Set
constant f = ∀ {d} → f ↓ d

≡-↓ : d ≡ e → fˢ ↓ d → fˢ ↓ e
≡-↓ refl = id

≤-↓ : e ≤ d → fˢ ↓ d → fˢ ↓ e
≤-↓ e≤d f↓ {n} u~v = ≡[≤] (+-monoˡ-≤ n e≤d) (f↓ u~v)

id↓ : causal {A = A} id
id↓ u~v = u~v

-- Constant functions never sense their inputs.
const↓ : constant {A = A} (const u)
const↓ _ _ _ = refl

map↓ : ∀ (f : A → B) → causal (map f)
map↓ f {n} {u} {v} u~v i i<n
  rewrite map-! f u i | map-! f v i | u~v i i<n = refl

-- map↓ f {n} {u} {v} u~v i i<n =
--   begin
--     map f u ! i
--   ≡⟨ map-! f u i ⟩
--     f (u ! i)
--   ≡⟨ cong f (u~v i i<n) ⟩
--     f (v ! i)
--   ≡˘⟨ map-! f v i ⟩
--     map f v ! i
--   ∎

infixr 5 _◂↓_
_◂↓_ : (b : B) → fˢ ↓ d → (b ◂ fˢ) ↓ suc d
(b ◂↓ f↓) u~v zero 0<1+d+n = refl
(b ◂↓ f↓) u~v (suc i) (s≤s i<d+n) = f↓ u~v i i<d+n

infixr 5 _◂*↓_
_◂*↓_ : (bs : Vec B e) → fˢ ↓ d → (bs ◂* fˢ) ↓ (e + d)
[]       ◂*↓ f↓ = f↓
(b ∷ bs) ◂*↓ f↓ = b ◂↓ bs ◂*↓ f↓

delay*ˢ : Vec A n → A →ˢ A
delay*ˢ as = as ◂* id

delayˢ : A → A →ˢ A
delayˢ a = delay*ˢ [ a ]

-- delayˢ a = a ◂ id
-- delayˢ = _◃_

delay*↓ : (as : Vec A d) → delay*ˢ as ↓ d
delay*↓ as = ≡-↓ (+-identityʳ _) (as ◂*↓ id↓)

delay↓ : ∀ (a : A) → contractive (delayˢ a)
delay↓ a = [ a ] ◂*↓ id↓

-- Sequential composition adds delays.
infixr 9 _∘↓_
_∘↓_ : gˢ ↓ e → fˢ ↓ d → gˢ ∘ fˢ ↓ e + d
_∘↓_ {e = e} {d = d} g↓ f↓ {n} rewrite +-assoc e d n = g↓ ∘ f↓

∘↓-map : gˢ ↓ e → (f : A → B) → (gˢ ∘ map f) ↓ e
∘↓-map {e = e} g↓ f = ≡-↓ (+-identityʳ e) (g↓ ∘↓ map↓ f)

-- Parallel composition with equal lags
infixr 7 _⊗↓≡_
_⊗↓≡_ : fˢ ↓ d → gˢ ↓ d → fˢ ⊗ gˢ ↓ d
_⊗↓≡_ {fˢ = fˢ} {gˢ = gˢ} f↓ g↓ {n} {u = u} {v} u~v i i<n =
  begin
    (fˢ ⊗ gˢ) u ! i
  ≡⟨⟩
    zip (fˢ (map proj₁ u) , gˢ (map proj₂ u)) ! i
  ≡⟨ zip-! _ i ⟩
    fˢ (map proj₁ u) ! i , gˢ (map proj₂ u) ! i
  ≡⟨ cong₂ _,_ (∘↓-map f↓ proj₁ u~v i i<n)
               (∘↓-map g↓ proj₂ u~v i i<n) ⟩
    fˢ (map proj₁ v) ! i , gˢ (map proj₂ v) ! i
  ≡˘⟨ zip-! _ i ⟩
    zip (fˢ (map proj₁ v) , gˢ (map proj₂ v)) ! i
  ≡⟨⟩
    (fˢ ⊗ gˢ) v ! i
  ∎

-- Parallel composition with arbitrary lags
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

infix 0 _→⁰_ _→¹_
_→⁰_ _→¹_ : Set → Set → Set
A →⁰ B = A →[ 0 ] B  -- causal
A →¹ B = A →[ 1 ] B  -- contractive

coerceᵈ : d ≡ e → (A →[ d ] B) → (A →[ e ] B)
coerceᵈ refl = id

infixr 5 _◂ᵈ_
_◂ᵈ_ : B → (A →[ d ] B) → (A →[ suc d ] B)
b ◂ᵈ mk f↓ = mk (b ◂↓ f↓)

infixr 5 _◂*ᵈ_
_◂*ᵈ_ : Vec B e → (A →[ d ] B) → (A →[ e + d ] B)
bs ◂*ᵈ mk f↓ = mk (bs ◂*↓ f↓)

idᵈ : A →⁰ A
idᵈ = mk id↓

-- Sequential composition
infixr 9 _∘ᵈ_
_∘ᵈ_ : (B →[ e ] C) → (A →[ d ] B) → (A →[ e + d ] C)
mk g↓ ∘ᵈ mk f↓ = mk (g↓ ∘↓ f↓)

-- Parallel composition
infixr 7 _⊗ᵈ_
_⊗ᵈ_ : (A →[ d ] C) → (B →[ e ] D) → (A × B →[ d ⊓ e ] C × D)
mk f↓ ⊗ᵈ mk g↓ = mk (f↓ ⊗↓ g↓)

constᵈ : (u : Stream B) → A →⁰ B
constᵈ u = mk (const↓ {u = u})

mapᵈ : (A → B) → (A →⁰ B)
mapᵈ f = mk (map↓ f)

delay*ᵈ : Vec A d → A →[ d ] A
delay*ᵈ as = coerceᵈ (+-identityʳ _) (as ◂*ᵈ idᵈ)

delayᵈ : A → A →¹ A
delayᵈ a = a ◂ᵈ idᵈ

-- delayᵈ a = mk (delay↓ a)

open import Data.Bool hiding (_≤_; _<_)

-- A stream function whose fixed point is a toggle flip-flop without enable.
toggleᵈ′ : Bool →¹ Bool
toggleᵈ′ = mapᵈ not ∘ᵈ delayᵈ false


-- Package seed type and value with seed-parametrized coalgebra to get a Mealy
-- machine, denoting a causal stream function.
infix 0 _→ᶜ_
record _→ᶜ_ (A B : Set) : Set₁ where
  constructor mk
  field
    {S} : Set
    s₀ : S
    h : A × S → B × S

stepsᶜ : (A →ᶜ B) × Vec A n → (A →ᶜ B) × Vec B n
stepsᶜ {A} {B} (mk {S = S} s h , as) = let bs , s′ = go (as , s) in mk s′ h , bs
 where
   go : Vec A n × S → Vec B n × S
   go ([] , s) = [] , s
   go (x ∷ u , sᵢ) =
     let y , s′  = h  (x  , sᵢ)
         ys , sₒ = go (u , s′)
     in
       y ∷ ys , sₒ

runᶜ : (A →ᶜ B) → (A →⁰ B)
runᶜ {A} {B} (mk {S} s h) = mk (go↓ s)
 where
   go : S → A →ˢ B
   head (go s u) = proj₁ (h (head u , s))
   tail (go s u) = go (proj₂ (h (head u , s))) (tail u)

   go↓ : (s : S) → causal (go s)
   go↓ s u~v zero (s≤s _) rewrite ≡[]-head u~v = refl
   go↓ s {u = u} {v} u~v (suc i) (s≤s i<n)
     rewrite ≡[]-head u~v | go↓ (proj₂ (h (head v , s))) (≡[]-tail u~v) i i<n
     = refl

mapᶜ : (A → B) → (A →ᶜ B)
mapᶜ f = mk tt λ (a , tt) → f a , tt

infixr 9 _∘ᶜ_
_∘ᶜ_ : B →ᶜ C → A →ᶜ B → A →ᶜ C
mk v g ∘ᶜ mk u f = mk (u , v) λ (a , (u , v)) →
  let b , s′ = f (a , u)
      c , t′ = g (b , v)
  in
    c , (s′ , t′)

infixr 7 _⊗ᶜ_
_⊗ᶜ_ : (A →ᶜ C) → (B →ᶜ D) → (A × B →ᶜ C × D)
mk u f ⊗ᶜ mk v g = mk (u , v) λ ((a , b) , u , v) →
  let c , s′ = f (a , u)
      d , t′ = g (b , v)
  in
    (c , d) , (s′ , t′)

-- d-lagging automaton, denoting a d-lagging stream function
infix 0 _⇒[_]_
_⇒[_]_ : Set → ℕ → Set → Set₁
A ⇒[ d ] B = Vec B d × (A →ᶜ B)

run⇒ : (A ⇒[ d ] B) → (A →[ d ] B)
run⇒ (bs , f) = coerceᵈ (+-identityʳ _) (bs ◂*ᵈ runᶜ f)

infix 0 _⇒⁰_ _⇒¹_
_⇒⁰_ _⇒¹_ : Set → Set → Set₁
A ⇒⁰ B = A ⇒[ 0 ] B  -- Mealy (causal)
A ⇒¹ B = A ⇒[ 1 ] B  -- Moore (contractive)

-- Sequential composition
infixr 9 _∘ᵃ_
_∘ᵃ_ : (B ⇒[ e ] C) → (A ⇒[ d ] B) → (A ⇒[ e + d ] C)
(cs , g) ∘ᵃ (bs , f) = let g′ , cs′ = stepsᶜ (g , bs) in cs ++ cs′ , g′ ∘ᶜ f

-- Parallel composition with equal lags
infixr 7 _⊗≡ᵃ_
_⊗≡ᵃ_ : (A ⇒[ n ] C) → (B ⇒[ n ] D) → (A × B ⇒[ n ] C × D)
(cs , f) ⊗≡ᵃ (ds , g) = v.zip cs ds , f ⊗ᶜ g

-- TODO: Parallel composition with arbitrary lags, or decide not to. The tricky
-- bit is incorporating surplus leading values into the laggier automaton's
-- causal representation. We could replace the state of that machine with a list
-- × the old state. Or with a nonempty list ⊎ the old state. Wait and see.
