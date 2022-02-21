{-# OPTIONS --guardedness #-}

-- This version defines and uses ! instead of take. Proofs are simpler and more
-- readily generalized beyond streams.

module StreamAt where

open import Function using (_∘_; id; const)
open import Data.Product as × hiding (map; zip) -- using (Σ; ∃; _×_; _,_; proj₁; proj₂)
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

open Stream public

infix 8 _!_
_!_ : Stream A → ℕ → A
s ! zero  = head s
s ! suc i = tail s ! i

-- Stream functions
infix 0 _→ˢ_
_→ˢ_ : Set → Set → Set
A →ˢ B = Stream A → Stream B

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

≡[≤] : ∀ {s t : Stream A} → m ≤ n → s ≡[ n ] t → s ≡[ m ] t
≡[≤] m≤n s∼ₙt i i<m = s∼ₙt i (≤-trans i<m m≤n)

-- Variation (unused)
≡[+] : {s : Stream A} {t : Stream A} → s ≡[ m + n ] t → s ≡[ m ] t
≡[+] s∼t = ≡[≤] (m≤m+n _ _) s∼t

-- Input influence is delayed by at least d steps.
delayed : ℕ → (A →ˢ B) → Set
delayed d f = ∀ {n s t} → s ≡[ n ] t → f s ≡[ d + n ] f t

causal : (A →ˢ B) → Set
causal = delayed 0

contractive : (A →ˢ B) → Set
contractive = delayed 1

constant : (A →ˢ B) → Set
constant f = ∀ {d} → delayed d f

delayed-≡ : ∀ {f : A →ˢ B} → d ≡ e → delayed d f → delayed e f
delayed-≡ {f = f} refl = id

delayed-≤ : ∀ {f : A →ˢ B} → e ≤ d → delayed d f → delayed e f
delayed-≤ e≤d delayed-d {n} s∼t = ≡[≤] (+-monoˡ-≤ n e≤d) (delayed-d s∼t)


-- Constant functions never sense their inputs.
const-is-constant : {bs : Stream B} → constant (const {B = Stream A} bs)
const-is-constant _ _ _ = refl

map-is-causal : ∀ (f : A → B) → causal (map f)
map-is-causal f {n} {s} {t} s∼t i i<n
  rewrite map-! f s i | map-! f t i | s∼t i i<n = refl

-- map-is-causal f {n} {s} {t} s∼t i i<n =
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

delay-is-contractive : ∀ (a : A) → contractive (delayˢ a)
delay-is-contractive _ s∼t  zero   _ = refl
delay-is-contractive _ s∼t (suc i) (s≤s i<n) = s∼t i i<n

-- delay-is-contractive a {suc n} {s} {t} s∼t (suc i) (s≤s i<n) =
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
delayed-∘ : ∀ {f : A →ˢ B} {g : B →ˢ C} →
  delayed e g → delayed d f → delayed (e + d) (g ∘ f)
delayed-∘ {e = e} {d} delayed-g delayed-f {n} rewrite +-assoc e d n =
  delayed-g ∘ delayed-f

delayed-∘-map : ∀ {f : A → B} {g : B →ˢ C} → delayed e g → delayed e (g ∘ map f)
delayed-∘-map {e = e} {f = f} {g} delayed-g =
  delayed-≡ (+-identityʳ e) (delayed-∘ delayed-g (map-is-causal f))

-- Parallel composition requires equal delays.
delayed-⊗-≡ : ∀ {f : A →ˢ C} {g : B →ˢ D} →
  delayed d f → delayed d g → delayed d (f ⊗ g)

-- Parallel composition with equal delays
delayed-⊗-≡ {f = f} {g} delayed-f delayed-g {n} {s = s} {t} s∼t i i<n =
  begin
    (f ⊗ g) s ! i
  ≡⟨⟩
    zip (f (map proj₁ s) , g (map proj₂ s)) ! i
  ≡⟨ zip-! _ i ⟩
    f (map proj₁ s) ! i , g (map proj₂ s) ! i
  ≡⟨ cong₂ _,_ (delayed-∘-map delayed-f s∼t i i<n)
               (delayed-∘-map delayed-g s∼t i i<n) ⟩
    f (map proj₁ t) ! i , g (map proj₂ t) ! i
  ≡˘⟨ zip-! _ i ⟩
    zip (f (map proj₁ t) , g (map proj₂ t)) ! i
  ≡⟨⟩
    (f ⊗ g) t ! i
  ∎

delayed-⊗ : ∀ {f : A →ˢ C} {g : B →ˢ D} →
  delayed d f → delayed e g → delayed (d ⊓ e) (f ⊗ g)
delayed-⊗ del-f del-g =
  delayed-⊗-≡ (delayed-≤ (m⊓n≤m _ _) del-f) (delayed-≤ (m⊓n≤n _ _) del-g)

-- TODO: Try defining delayed-⊗ directly rather than via delayed-⊗-≡ .

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

infix 0 _→⁰_ _→¹_
_→⁰_ _→¹_ : Set → Set → Set
A →⁰ B = A →[ 0 ] B  -- causal
A →¹ B = A →[ 1 ] B  -- contractive

map⁰ : (A → B) → (A →[ 0 ] B)
map⁰ f = map f , map-is-causal f

delay¹ : A → A →¹ A
delay¹ a = delayˢ a , delay-is-contractive a

open import Data.Bool

-- A stream function whose fixed point is a toggle flip-flop without enable.
toggle′ : Bool →¹ Bool
toggle′ = map⁰ not ∘ᵈ delay¹ false
