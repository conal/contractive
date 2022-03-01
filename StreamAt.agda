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
≤-↓ e≤d f↓ {n} s~t = ≡[≤] (+-monoˡ-≤ n e≤d) (f↓ s~t)

id↓ : causal {A = A} id
id↓ s~t = s~t

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

infixr 5 _◂↓_
_◂↓_ : (b : B) → fˢ ↓ d → (b ◂ fˢ) ↓ suc d
(b ◂↓ f↓) s~t zero 0<1+d+n = refl
(b ◂↓ f↓) s~t (suc i) (s≤s i<d+n) = f↓ s~t i i<d+n

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

-- delay↓ a = a ◂↓ id↓

-- delay↓ : ∀ (a : A) → contractive (delayˢ a)
-- delay↓ _ s~t  zero       _     = refl
-- delay↓ _ s~t (suc i) (s≤s i<n) = s~t i i<n

-- delay↓ a {suc n} {s} {t} s~t (suc i) (s≤s i<n) =
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

-- Parallel composition with equal lags
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

constᵈ : (s : Stream B) → A →⁰ B
constᵈ s = mk (const↓ {s = s})

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
    state : S
    h : A × S → B × S

stepsᶜ : (A →ᶜ B) × Vec A n → (A →ᶜ B) × Vec B n
stepsᶜ {A} {B} (mk {S = S} c h , as) = let bs , c′ = go (as , c) in mk c′ h , bs
 where
   go : Vec A n × S → Vec B n × S
   go ([] , c) = [] , c
   go (x ∷ xs , cᵢ) =
     let y , c′  = h  (x  , cᵢ)
         ys , cₒ = go (xs , c′)
     in
       y ∷ ys , cₒ

-- TODO: Rename stream variables s & t to xs & ys, freeing up s & t for states.

runᶜ : (A →ᶜ B) → (A →[ 0 ] B)
runᶜ {A} {B} (mk {S} c h) = mk (go↓ c)
 where
   go : S → A →ˢ B
   head (go c xs) = proj₁ (h (head xs , c))
   tail (go c xs) = go (proj₂ (h (head xs , c))) (tail xs)

   go↓ : (c : S) → causal (go c)
   go↓ c s~t zero (s≤s _) rewrite ≡[]-head s~t = refl
   go↓ c {s = s} {t} s~t (suc i) (s≤s i<n)
     rewrite ≡[]-head s~t | go↓ (proj₂ (h (head t , c))) (≡[]-tail s~t) i i<n
     = refl

mapᶜ : (A → B) → (A →ᶜ B)
mapᶜ f = mk {S = ⊤} tt λ (a , tt) → f a , tt

infixr 9 _∘ᶜ_
_∘ᶜ_ : B →ᶜ C → A →ᶜ B → A →ᶜ C
mk t g ∘ᶜ mk s f = mk (s , t) λ (a , (s , t)) →
  let b , s′ = f (a , s)
      c , t′ = g (b , t)
  in
    c , (s′ , t′)

infixr 7 _⊗ᶜ_
_⊗ᶜ_ : (A →ᶜ C) → (B →ᶜ D) → (A × B →ᶜ C × D)
mk s f ⊗ᶜ mk t g = mk (s , t) λ ((a , b) , s , t) →
  let c , s′ = f (a , s)
      d , t′ = g (b , t)
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
A ⇒⁰ B = A ⇒[ 0 ] B  -- causal/Mealy
A ⇒¹ B = A ⇒[ 1 ] B  -- contractive/Moore

-- Sequential composition
infixr 9 _∘ᵃ_
_∘ᵃ_ : (B ⇒[ e ] C) → (A ⇒[ d ] B) → (A ⇒[ e + d ] C)
(cs , g) ∘ᵃ (bs , f) = let g′ , cs′ = stepsᶜ (g , bs) in cs ++ cs′ , g′ ∘ᶜ f

-- Parallel composition with equal lags
infixr 7 _⊗≡ᵃ_
_⊗≡ᵃ_ : (A ⇒[ n ] C) → (B ⇒[ n ] D) → (A × B ⇒[ n ] C × D)
(cs , f) ⊗≡ᵃ (ds , g) = v.zip cs ds , f ⊗ᶜ g

-- TODO: Parallel composition with arbitrary lags, or decide not to.
