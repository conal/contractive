{-# OPTIONS --guardedness #-}

module Stream where

open import Function using (_∘_; id; const)
open import Data.Product as × using (Σ; ∃; _×_; _,_; proj₁; proj₂)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Vec as v using (Vec; []; _∷_)
open import Data.Vec.Properties

open import Relation.Binary.PropositionalEquality ; open ≡-Reasoning

private variable
  A B C D : Set
  m n d e : ℕ

record Stream A : Set where
  coinductive
  constructor _◃_ 
  field
    head : A
    tail : Stream A

open Stream

take : Stream A → {n : ℕ} → Vec A n
take s {zero } = []
take s {suc _} = head s ∷ take (tail s)

-- TODO: maybe move n to front for convenient partial application.
-- TODO: maybe make n argument explicit for clearer proofs.

drop : ℕ → Stream A → Stream A
drop  zero   s = s
drop (suc n) s = drop n (tail s)


take-+ : ∀ {m n} {s : Stream A} → take s {m} ≡ v.take m (take s {m + n})
take-+ {m = zero } = refl
take-+ {m = suc m} {n} {s} =
  begin
    take s {suc m}
  ≡⟨⟩
    head s ∷ take (tail s) {m}
  ≡⟨ cong (head s ∷_) take-+ ⟩
    head s ∷ v.take m (take (tail s) {m + n})
  ≡˘⟨ unfold-take _ _ _ ⟩
    v.take (suc m) (head s ∷ take (tail s) {m + n})
  ≡⟨⟩
    v.take (suc m) (take s {suc (m + n)})
  ∎

drop-+ : ∀ m {n} {s : Stream A} → drop (m + n) s ≡ drop n (drop m s) -- TODO: ≗
drop-+  zero   = refl
drop-+ (suc m) = drop-+ m

-- drop-+ (suc m) {n} {s} =
--   begin
--     drop (suc m + n) s
--   ≡⟨⟩
--     drop (m + n) (tail s)
--   ≡⟨ drop-+ m ⟩
--     drop n (drop m (tail s))
--   ≡⟨⟩
--     drop n (drop (suc m) s)
--   ∎


infix 0 _→ˢ_
_→ˢ_ : Set → Set → Set
A →ˢ B = Stream A → Stream B

map : (A → B) → (A →ˢ B)
head (map f s) = f (head s)
tail (map f s) = map f (tail s)

take-map : ∀ (f : A → B) s {n} → take (map f s) {n} ≡ v.map f (take s)
take-map f s {zero } = refl
take-map f s {suc n} rewrite take-map f (tail s) {n} = refl

-- take-map s f {suc n} =
--   begin
--     take (map f s)
--   ≡⟨⟩
--     f (head s) ∷ take (map f (tail s))
--   ≡⟨ cong (f (head s) ∷_) (take-map (tail s) f) ⟩
--     f (head s) ∷ v.map f (take (tail s))
--   ≡⟨⟩
--     v.map f (take s)
--   ∎

zip : Stream A × Stream B → Stream (A × B)
head (zip (xs , ys)) = head xs , head ys
tail (zip (xs , ys)) = zip (tail xs , tail ys)

take-zip : ∀ ((s , t) : Stream A × Stream B) {n} →
  take (zip (s , t)) {n} ≡ v.zip (take s) (take t)
take-zip (s , t) {zero } = refl
take-zip (s , t) {suc n} rewrite take-zip (tail s , tail t) {n} = refl

unzip : Stream (A × B) → Stream A × Stream B
unzip zs = map proj₁ zs , map proj₂ zs

infixr 7 _⊗_
_⊗_ : (A →ˢ C) → (B →ˢ D) → (A × B →ˢ C × D)
f ⊗ g = zip ∘ ×.map f g ∘ unzip

-- TODO: take {m} ≗ v.take m ∘ take {m + n}  (after swapping take's arguments)

infix 4 _≡[_]_
_≡[_]_ : Stream A → ℕ → Stream A → Set
s ≡[ n ] t = take s {n} ≡ take t

-- Weaken equivalence
≡[+] : {s : Stream A} {t : Stream A} → s ≡[ m + n ] t → s ≡[ m ] t
≡[+] {m = m} {n = n} {s = s} {t} eq =
  begin
    take s {m}
  ≡⟨ take-+ ⟩
    v.take m (take s {m + n})
  ≡⟨ cong (v.take m) eq ⟩
    v.take m (take t {m + n})
  ≡˘⟨ take-+ ⟩
    take t {m}
  ∎

-- Input influence is delayed by at least d steps.
delayed : ℕ → (A →ˢ B) → Set
delayed d f = ∀ {n s t} → s ≡[ n ] t → f s ≡[ d + n ] f t

causal : (A →ˢ B) → Set
causal = delayed 0

contractive : (A →ˢ B) → Set
contractive = delayed 1

constant : (A →ˢ B) → Set
constant f = ∀ {d} → delayed d f

-- Constant functions never sense their inputs.
const-constant : {bs : Stream B} → constant (const {B = Stream A} bs)
const-constant s∼t = refl

map-causal : ∀ (f : A → B) → causal (map f)
map-causal f {zero } s∼t = refl
map-causal f {suc n} {s = s} {t} s∼t =
  begin
    take (map f s)
  ≡⟨ take-map f s ⟩
    v.map f (take s)
  ≡⟨ cong (v.map f) s∼t ⟩
    v.map f (take t)
  ≡˘⟨ take-map f t ⟩
    take (map f t)
  ∎

delayˢ : A → A →ˢ A
delayˢ = _◃_

delay-contractive : ∀ (a : A) → contractive (delayˢ a)
delay-contractive _ {n = zero } _ = refl
delay-contractive _ {n = suc n} s∼t rewrite s∼t = refl

-- delay-contractive a {n = suc n} s t s∼t =
--   begin
--     take (a ◃ s)
--   ≡⟨⟩
--     a ∷ head s ∷ take (tail s)
--   ≡⟨ cong (a ∷_) s∼t ⟩
--     a ∷ head t ∷ take (tail t)
--   ≡⟨⟩
--     take (a ◃ t)
--   ∎

-- Sequential composition adds delays.
delayed-∘ : ∀ {f : A →ˢ B} {g : B →ˢ C} →
  delayed e g → delayed d f → delayed (e + d) (g ∘ f)
delayed-∘ {e = e} {d} delayed-g delayed-f {n} rewrite +-assoc e d n =
  delayed-g ∘ delayed-f

-- Parallel composition requires equal delays.
-- TODO: use _⊓_ (min) of delays instead.
delayed-⊗-≡ : ∀ {f : A →ˢ C} {g : B →ˢ D} →
  delayed d f → delayed d g → delayed d (f ⊗ g)
delayed-⊗-≡ {d = d} {f} {g} delayed-f delayed-g {n} {s} {t} s∼t =
  begin
    take ((f ⊗ g) s)
  ≡⟨⟩
    take (zip (f (map proj₁ s) , g (map proj₂ s))) {d + n}
  ≡⟨ take-zip _ ⟩
    v.zip (take (f (map proj₁ s))) (take (g (map proj₂ s)))
  ≡⟨ cong₂ v.zip (delayed-f (map-causal proj₁ s∼t))
                 (delayed-g (map-causal proj₂ s∼t)) ⟩
    v.zip (take (f (map proj₁ t))) (take (g (map proj₂ t)))
  ≡˘⟨ take-zip _ ⟩
    take (zip (f (map proj₁ t) , g (map proj₂ t))) {d + n}
  ≡⟨⟩
    take ((f ⊗ g) t)
  ∎

≡[≤] : ∀ {s t : Stream A} → m ≤ n → s ≡[ n ] t → s ≡[ m ] t
≡[≤] z≤n s∼ₙt = refl
≡[≤] {s = s} {t} (s≤s {m} m≤n) s∼ₙt with heads≡ , tails≡ ← ∷-injective s∼ₙt =
  begin
    take s {suc m}
  ≡⟨⟩
    head s ∷ take (tail s) {m}
  ≡⟨ cong₂ _∷_ heads≡ (≡[≤] {s = tail s} {tail t} m≤n tails≡) ⟩
    head t ∷ take (tail t) {m}
  ≡⟨⟩
    take t {suc m}
  ∎

-- I couldn't find this one in Data.Nat.Properties
≤+ʳ : e ≤ d → e + n ≤ d + n
≤+ʳ z≤n = m≤n+m _ _
≤+ʳ (s≤s e≤d) = s≤s (≤+ʳ e≤d)

delayed-≤ : ∀ {f : A →ˢ B} → e ≤ d → delayed d f → delayed e f
delayed-≤ e≤d del-e {n} s∼t = ≡[≤] (≤+ʳ e≤d) (del-e s∼t)

delayed-⊗ : ∀ {f : A →ˢ C} {g : B →ˢ D} →
  delayed d f → delayed e g → delayed (d ⊓ e) (f ⊗ g)
delayed-⊗ del-f del-g s∼t =
  delayed-⊗-≡ (delayed-≤ (m⊓n≤m _ _) del-f) (delayed-≤ (m⊓n≤n _ _) del-g) s∼t

-- Stream functions delayed by d
infix 0 _→[_]_
_→[_]_ : Set → ℕ → Set → Set
A →[ d ] B = Σ (A →ˢ B) (delayed d)

-- Sequential composition
infixr 9 _∘ᵈ_
_∘ᵈ_ : (B →[ e ] C) → (A →[ d ] B) → (A →[ e + d ] C)
(g , delayed-g) ∘ᵈ (f , delayed-f) = g ∘ f , delayed-∘ delayed-g delayed-f

-- Parallel composition
infixr 7 _⊗ᵈ_
_⊗ᵈ_ : (A →[ d ] C) → (B →[ e ] D) → (A × B →[ d ⊓ e ] C × D)
(f , delayed-f) ⊗ᵈ (g , delayed-g) = f ⊗ g , delayed-⊗ delayed-f delayed-g

-- TODO: use _⊓_ (min) of delays

infix 0 _→⁰_ _→¹_
_→⁰_ _→¹_ : Set → Set → Set
A →⁰ B = A →[ 0 ] B  -- causal
A →¹ B = A →[ 1 ] B  -- contractive

open import Data.Bool

invˢ : Bool →ˢ Bool
invˢ = map not

map⁰ : (A → B) → (A →[ 0 ] B)
map⁰ f = map f , map-causal f

delay¹ : A → A →¹ A
delay¹ a = delayˢ a , delay-contractive a

-- A stream function whose fixed point is a toggle flip-flop without enable.
toggle′ : Bool →¹ Bool
toggle′ = map⁰ not ∘ᵈ delay¹ false
