module TimedCat where

open import Level using (0ℓ)
open import Data.Nat
open import Data.Nat.Properties using (+-assoc)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality as ≡

open import Categorical.Raw renaming (xor to ⊕; Bool to 𝔹)
open import Functions 0ℓ

-- A category of timed computation. Objects are time tries, and morphisms are
-- computable functions between bit tries (easily generalized to arbitrary
-- atomic types). The relationship to regular computable functions is a simple
-- functor that forgets times. Later, we'll swap out functions (denotation) for
-- a compilable representation, again with a functor back to semantics. As
-- always, implementation correctness is semantic homomorphicity/functoriality.

private variable a b c : Set

infixr 6 _`⊎_
data Shape : Set where
  `⊥ : Shape
  `⊤ : Shape
  _`⊎_  : Shape → Shape → Shape

private variable ρ σ : Shape

infixr 6 _▿_
data Trie (a : Set) : Shape → Set where
  1̇ : Trie a `⊥
  İ : a → Trie a `⊤
  _▿_ : Trie a ρ → Trie a σ → Trie a (ρ `⊎ σ)

private variable u v : Trie a ρ

𝕋 : Set   -- "Time", which could be ℚ or ℝ
𝕋 = ℕ

private variable n : ℕ ; s t d e : 𝕋

map : (a → b) → Trie a ρ → Trie b ρ
map f 1̇ = 1̇
map f (İ x) = İ (f x)
map f (u ▿ v) = map f u ▿ map f v

map-id : ∀ {u : Trie a ρ} → map id u ≡ u
map-id {u = 1̇} = refl
map-id {u = İ x} = refl
map-id {u = u ▿ v} = cong₂ _▿_ map-id map-id

map-∘ : ∀ {f : a → b} {g : b → c} → map (g ∘ f) u ≡ map g (map f u)
map-∘ {u = 1̇} = refl
map-∘ {u = İ x} = refl
map-∘ {u = u ▿ v} = cong₂ _▿_ map-∘ map-∘

map-cong : ∀ {f g : a → b} → f ≗ g → map f u ≡ map g u
map-cong {u = 1̇} f≗g = refl
map-cong {u = İ x} f≗g = cong İ (f≗g x)
map-cong {u = u ▿ v} f≗g = cong₂ _▿_ (map-cong f≗g) (map-cong f≗g)

-- Two corollaries involving addition:

map-0-+ : map (0 +_) u ≡ u
map-0-+ = map-id

map-+-+ : map ((d + e) +_) u ≡ map (d +_) (map (e +_) u)
map-+-+ {d = d} {e} = trans (map-cong (+-assoc d e)) map-∘

-- Objects: time tries
record Obj : Set where
  constructor obj
  field
    {shape} : Shape
    times : Trie 𝕋 shape
open Obj public

private variable A B C D S : Obj

module timed-obj-instances where instance

  products : Products Obj
  products = record { ⊤ = obj 1̇ ; _×_ = λ { (obj u) (obj v) → obj (u ▿ v) } }

  boolean : Boolean Obj
  boolean = record { Bool = obj (İ 0) }

Retime : (h : 𝕋 → 𝕋) → Obj → Obj
Retime h (obj ts) = obj (map h ts)

Delay : 𝕋 → Obj → Obj
Delay d = Retime (d +_)

-- Morphisms: functions on bit tries
infix 0 _⇨_
record _⇨_ (A B : Obj) : Set where
  constructor mk
  field
    f : Trie 𝔹 (shape A) → Trie 𝔹 (shape B)

module timed-cat-instances where instance

  category : Category _⇨_
  category = record { id = mk id ; _∘_ = λ (mk g) (mk f) → mk (g ∘ f) }

  cartesian : Cartesian _⇨_
  cartesian = record
    {  !  = mk λ _ → 1̇
    ; _▵_ = λ (mk f) (mk g) → mk λ x → f x ▿ g x
    ; exl = mk λ { (u ▿ v) → u }
    ; exr = mk λ { (u ▿ v) → v }
    }

  logic : Logic _⇨_
  logic = record
    { false = mk λ { 1̇ → İ 𝕗 }
    ; true  = mk λ { 1̇ → İ 𝕥 }
    ; not   = mk λ { (İ x) → İ (not x) }
    ; ∧     = mk λ { (İ x ▿ İ y) → İ (∧ (x , y)) }
    ; ∨     = mk λ { (İ x ▿ İ y) → İ (∨ (x , y)) }
    ; xor   = mk λ { (İ x ▿ İ y) → İ (⊕ (x , y)) }
    ; cond  = mk λ { (İ b ▿ u ▿ v) → cond (b , u , v) }
    }

retime : ∀ {g h} → (A ⇨ B) → (Retime g A ⇨ Retime h B)
retime (mk f) = mk f

delay : (A ⇨ B) → (Delay d A ⇨ Delay d B)
delay = retime
-- delay (mk f) = mk f

pause : A ⇨ Delay d A
pause = mk id

-- Progressively delayed objects
Delays : 𝕋 → Obj → ℕ → Obj
Delays d A zero = ⊤
Delays d A (suc n) = A × Delay d (Delays d A n)

-- Untimed pipelining (map)
pipe′ : (a → b) → ∀ n → V a n → V b n
pipe′ f zero tt = tt
pipe′ f (suc n) (a , as) = f a , pipe′ f n as

-- Categorical formulation
pipe″ : (a → b) → ∀ n → V a n → V b n
pipe″ f zero = id
pipe″ f (suc n) = f ⊗ pipe″ f n

-- Temporal version
pipe : (A ⇨ B) → ∀ n → Delays d A n ⇨ Delays d B n
pipe f zero = id
pipe f (suc n) = f ⊗ delay (pipe f n)

-- Generalize pipe to mealy

mealy′ : ∀ {s} → (s × a → b × s) → ∀ n → s × V a n → V b n × s
mealy′ h zero (s , tt) = tt , s
mealy′ h (suc n) (s , (a , as)) = let b  , t = h (s , a )
                                      bs , u = mealy′ h n (t , as)
                                  in (b , bs) , u

mealy″ : ∀ {s} → (s × a → b × s) → ∀ n → s × V a n → V b n × s
mealy″ h  zero   = unitorⁱˡ ∘ unitorᵉʳ
mealy″ h (suc n) = assocˡ ∘ second (mealy″ h n) ∘ inAssocˡ h

subT : ∀ {u v : Trie 𝕋 ρ} → v ≡ u → obj u ⇨ obj v
subT refl = id

mealy : (S × A ⇨ B × Delay d S) →
  ∀ n → S × Delays d A n ⇨ Delays d B n × Delay (n * d) S
mealy h zero = unitorⁱˡ ∘ subT map-0-+ ∘ exl
mealy h (suc n) =
  assocˡ ∘ second (second (subT map-+-+) ∘ delay (mealy h n)) ∘ inAssocˡ h

-- pipe as mealy with empty state
pipeM : (A ⇨ B) → ∀ n → Delays d A n ⇨ Delays d B n
pipeM f n = unitorᵉʳ ∘ mealy (unitorⁱʳ ∘ f ∘ unitorᵉˡ) n ∘ unitorⁱˡ


---- Examples


-- Gate delay
γ : 𝕋
γ = 2

⊕γ ∧γ : 𝔹 × 𝔹 ⇨ Delay γ 𝔹
⊕γ = delay ⊕ ∘ pause
∧γ = delay ∧ ∘ pause

-- ⊕γ = pause ∘ ⊕
-- ∧γ = pause ∘ ∧

-- Possibly increment. Carry-in on left and carry-out on right.
up₁ : 𝔹 × 𝔹 ⇨ Delay γ (𝔹 × 𝔹)
up₁ = ⊕γ ▵ ∧γ

-- Conditionally increment an n-bit natural number
up : ∀ n → 𝔹 × Delays γ 𝔹 n ⇨ Delays γ (Delay γ 𝔹) n × Delay (n * γ) 𝔹
up = mealy up₁
