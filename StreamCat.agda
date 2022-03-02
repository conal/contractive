{-# OPTIONS --guardedness #-}

module StreamCat where

open import Function using (_∘_; id; const; _$_)
open import Data.Unit using (⊤; tt)
open import Data.Product as × hiding (map; zip)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Vec as v using (Vec; []; _∷_; [_]; _++_)
open import Data.Vec.Properties
open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning

infixr 5 _◃_

record Stream A : Set where
  coinductive
  constructor _◃_ 
  field
    head : A
    tail : Stream A

open Stream public

private variable
  A B C D : Set
  m n d e i : ℕ
  u v : Stream A

infix 4 _≈_
record _≈_ (u v : Stream A) : Set where
  coinductive
  constructor _◃_
  field
    head : head u ≡ head v
    tail : tail u ≈ tail v

open _≈_ public

-- Alternatively, `∀ i → u ! i ≡ v ! i`.

≈-refl : u ≈ u
head ≈-refl = refl
tail ≈-refl = ≈-refl

infixl 8 _!_
_!_ : Stream A → ℕ → A
u ! zero  = head u
u ! suc i = tail u ! i

!-cong : ∀ i → u ≈ v → u ! i ≡ v ! i
!-cong  zero   =            head
!-cong (suc i) = !-cong i ∘ tail

-- -- Or this order?
-- !-cong′ : u ≈ v → ∀ i → u ! i ≡ v ! i
-- !-cong′ u≈v  zero   = head u≈v
-- !-cong′ u≈v (suc i) = !-cong′ (tail u≈v) i

repeat : A → Stream A
head (repeat a) = a
tail (repeat a) = repeat a


-- Stream functions
infix 0 _→ˢ_
_→ˢ_ : Set → Set → Set
A →ˢ B = Stream A → Stream B

infixr 5 _◃*_
_◃*_ : Vec A n → A →ˢ A
[]       ◃* u = u
(x ∷ xs) ◃* u = x ◃ (xs ◃* u)

splitAt : ∀ m (xs : Stream A) →
          ∃₂ λ (ys : Vec A m) (zs : Stream A) → xs ≈ ys ◃* zs
splitAt  zero   xs = [] , xs , ≈-refl
splitAt (suc m) xs with ys , zs , p ← splitAt m (tail xs) =
  head xs ∷ ys , zs , refl ◃ p

take : ∀ m (xs : Stream A) → Vec A m
take m xs with ys , _ , _ ← splitAt m xs = ys

drop : ℕ → A →ˢ A
drop m xs with _ , zs , _ ← splitAt m xs = zs

drop-! : ∀ e → drop e u ! i ≡ u ! (e + i)
drop-!  zero   = refl
drop-! (suc e) = drop-! e

-- drop-! {u = u} {i} (suc e) =
--   begin
--     drop (suc e) u ! i
--   ≡⟨⟩
--     drop e (tail u) ! i
--   ≡⟨ drop-! e ⟩
--     tail u ! (e + i)
--   ≡⟨⟩
--     u ! (suc e + i)
--   ∎

infix 4 _≈̂_
_≈̂_ : (A →ˢ B) → (A →ˢ B) → Set
f ≈̂ g = ∀ {u} → f u ≈ g u

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

-- Prefix-equivalence
infix 4 _≡[_]_
_≡[_]_ : Stream A → ℕ → Stream A → Set
u ≡[ n ] v = ∀ i → i < n → u ! i ≡ v ! i

-- Alternatively, take n u ≡ take n v

≡[]-head : u ≡[ suc n ] v → head u ≡ head v
≡[]-head u~v = u~v 0 (s≤s z≤n)

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

-- Another bit I've been meaning to state and prove: every stream function `f :
-- A →ˢ B` (semantics) lagging by `n` can be written as `bs ◂* g` where `b : Vec
-- B n` and `g : A →ˢ B`.

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

head-↓ : fˢ ↓ suc d → ∀ {u v} → head (fˢ u) ≡ head (fˢ v)
head-↓ {fˢ = fˢ} {d} f↓ {u} {v} =
  begin
    head (fˢ u)
  ≡⟨⟩
    fˢ u  ! 0
  ≡⟨ f↓ {n = 0} (λ { i () }) 0 (s≤s z≤n) ⟩
    fˢ v ! 0
  ≡⟨⟩
    head (fˢ v)
  ∎

drop∘↓ : ∀ e → fˢ ↓ e + d → drop e ∘ fˢ ↓ d
drop∘↓ {fˢ = fˢ} {d = d} e f↓ {n} {u} {v} u~v i i<d+n =
  begin
    (drop e ∘ fˢ) u ! i
  ≡⟨ drop-! e ⟩
    fˢ u ! (e + i)
  ≡⟨ f↓ u~v (e + i) 
        (subst (e + i <_) (sym (+-assoc e d n)) (+-monoʳ-< e i<d+n)) ⟩
    fˢ v ! (e + i)
  ≡˘⟨ drop-! e ⟩
    (drop e ∘ fˢ) v ! i
  ∎

tail↓ : fˢ ↓ suc d → tail ∘ fˢ ↓ d
tail↓ = drop∘↓ 1

-- tail↓ f↓ u~v i i<d+n = f↓ u~v (suc i) (s≤s i<d+n)

as-◂ : fˢ ↓ suc d → ∀ {any} → fˢ ≈̂ head (fˢ any) ◂ tail ∘ fˢ
head (as-◂ f↓) = head-↓ f↓
tail (as-◂ f↓) = ≈-refl

-- Main characterization theorem on lagging stream functions
as-◂* : ∀ e → fˢ ↓ e + d → ∀ {any} → fˢ ≈̂ take e (fˢ any) ◂* drop e ∘ fˢ
as-◂* zero f↓ = ≈-refl
head (as-◂* (suc e) f↓) = head-↓ f↓
tail (as-◂* (suc e) f↓) = as-◂* e (tail↓ f↓)

-- Since fˢ ↓ e + d → fˢ ↓ e, we could eliminate d from as-◂*. Wait and see how
-- uses of as-◂* work out. I think drop∘↓ will appear.

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

-- TODO: Consider instead defining bs ◂* f

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
infix 0 _→ᵈ_
record _→ᵈ_ (A B : Set) : Set where
  constructor mk
  field
    {f} : A →ˢ B
    {Δ} : ℕ  -- Lag: 0 (causal), 1 (contractive), etc
    f↓  : f ↓ Δ

-- coerceᵈ : d ≡ e → (A →[ d ] B) → (A →[ e ] B)
-- coerceᵈ refl = id

infixr 5 _◂ᵈ_
_◂ᵈ_ : B → (A →ᵈ B) → (A →ᵈ B)
b ◂ᵈ mk f↓ = mk (b ◂↓ f↓)

infixr 5 _◂*ᵈ_
_◂*ᵈ_ : Vec B e → (A →ᵈ B) → (A →ᵈ B)
bs ◂*ᵈ mk f↓ = mk (bs ◂*↓ f↓)

idᵈ : A →ᵈ A
idᵈ = mk id↓

-- Sequential composition
infixr 9 _∘ᵈ_
_∘ᵈ_ : (B →ᵈ C) → (A →ᵈ B) → (A →ᵈ C)
mk g↓ ∘ᵈ mk f↓ = mk (g↓ ∘↓ f↓)

-- Parallel composition
infixr 7 _⊗ᵈ_
_⊗ᵈ_ : (A →ᵈ C) → (B →ᵈ D) → (A × B →ᵈ C × D)
mk f↓ ⊗ᵈ mk g↓ = mk (f↓ ⊗↓ g↓)

-- constᵈ : (u : Stream B) → A →ᵈ B
-- constᵈ u = mk (const↓ {u = u})

mapᵈ : (A → B) → (A →ᵈ B)
mapᵈ f = mk (map↓ f)

delay*ᵈ : Vec A d → A →ᵈ A
delay*ᵈ as = as ◂*ᵈ idᵈ

delayᵈ : A → A →ᵈ A
delayᵈ a = a ◂ᵈ idᵈ

open import Data.Bool hiding (_≤_; _<_)

-- A stream function whose fixed point is a toggle flip-flop without enable.
toggleᵈ′ : Bool →ᵈ Bool
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

⟦_⟧ᶜ : (A →ᶜ B) → (A →ᵈ B)
⟦_⟧ᶜ {A} {B} (mk {S} s h) = mk (go↓ s)
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

open import Data.Vec.Bounded as B using (Vec≤; fromVec) renaming (_,_ to _⊣_)

infixr 5 _◂*ᶜ_
_◂*ᶜ_ : Vec B n → (A →ᶜ B) → (A →ᶜ B)
[] ◂*ᶜ f = f  -- Useful optimization? Proofs will be easier without.
_◂*ᶜ_ {B = B} {n = n} {A} bs₀ (mk {S = S} s₀ h) =
  -- Stash outputs in a bounded vector/FIFO
  mk {S = Vec≤ B n × S} (fromVec bs₀ , s₀) λ
    { (a , ([] ⊣ _) , s) → let b , s′ = h (a , s) in b , B.[] , s′
    ; (a , (b ∷ bs ⊣ m<n) , s) → b , (bs ⊣ <⇒≤ m<n) , s
    }

-- d-lagging automaton, denoting a d-lagging stream function
infix 0 _→ᵃ_
record _→ᵃ_ (A B : Set) : Set₁ where
  constructor mk
  field
    {Δ} : ℕ
    leading : Vec B Δ
    f : A →ᶜ B

open _→ᵃ_ using (Δ) public

⟦_⟧ : (A →ᵃ B) → (A →ᵈ B)
⟦ mk bs f ⟧ = bs ◂*ᵈ ⟦ f ⟧ᶜ

-- Sequential composition
infixr 9 _∘ᵃ_
_∘ᵃ_ : (B →ᵃ C) → (A →ᵃ B) → (A →ᵃ C)
mk cs g ∘ᵃ mk bs f = let g′ , cs′ = stepsᶜ (g , bs) in mk (cs ++ cs′) (g′ ∘ᶜ f)

private
  -- Parallel composition with equal lags
  infixr 7 _⊗≡ᵃ_
  _⊗≡ᵃ_ : (f : A →ᵃ C) (g : B →ᵃ D) ⦃ _ : Δ f ≡ Δ g ⦄ → (A × B →ᵃ C × D)
  (mk cs f ⊗≡ᵃ mk ds g) ⦃ refl ⦄ = mk (v.zip cs ds) (f ⊗ᶜ g)

  -- This equality constraint precludes a monoidal category.

private
  split : m ≤ n → Vec A n → Vec A m × Vec A (n ∸ m)
  split {m} {n} m≤n xs =
   let less-than-or-equal p = ≤⇒≤″ m≤n
       xsˡ , xsʳ , _ = v.splitAt m (subst (Vec _) (sym p) xs)
   in xsˡ , xsʳ

-- Parallel composition with arbitrary lags
infixr 7 _⊗ᵃ_
_⊗ᵃ_ : (f : A →ᵃ C) (g : B →ᵃ D) → (A × B →ᵃ C × D)
mk {Δ = m} cs f ⊗ᵃ mk {Δ = n} ds g =
  let csˡ , csʳ = split (m⊓n≤m m n) cs
      dsˡ , dsʳ = split (m⊓n≤n m n) ds
  in
    mk (v.zip csˡ dsˡ) ((csʳ ◂*ᶜ f) ⊗ᶜ (dsʳ ◂*ᶜ g))

-- TODO: Prove that ⟦_⟧ is functorial.
