module TimedCat where

open import Level using (0ℓ)
open import Data.Empty.Polymorphic
open import Data.Sum using (_⊎_)
open import Data.Nat
open import Data.Nat.Properties
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

infixr 1 _;_   -- unicode
_;_ : ∀ {ℓ} {a : Set ℓ} {x y z : a} → x ≡ y → y ≡ z → x ≡ z
_;_ = trans

infixr 6 _`⊎_
data Shape : Set where
  `⊥ : Shape
  `⊤ : Shape
  _`⊎_  : Shape → Shape → Shape

private variable ρ σ : Shape

⟦_⟧ : Shape → Set
⟦ `⊥ ⟧ = ⊥
⟦ `⊤ ⟧ = ⊤
⟦ ρ `⊎ σ ⟧ = ⟦ ρ ⟧ ⊎ ⟦ σ ⟧

-- Trie a ρ ≅ ⟦ ρ ⟧ → a

infixr 6 _▿_
data Trie (a : Set) : Shape → Set where
  1̇ : Trie a `⊥
  İ : a → Trie a `⊤
  _▿_ : Trie a ρ → Trie a σ → Trie a (ρ `⊎ σ)

private variable u v : Trie a ρ

𝕋 : Set   -- "Time", which could be ℚ or ℝ
𝕋 = ℕ

private variable m n : ℕ ; s t d e : 𝕋

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

-- Corollaries (map ∘ _+_ is a monoid homomorphism):

map-+-identityˡ : map (0 +_) u ≡ u
map-+-identityˡ = map-id

map-+-assoc : map ((d + e) +_) u ≡ map (d +_) (map (e +_) u)
map-+-assoc {d = d} {e} = map-cong (+-assoc d e) ; map-∘

map-+-comm : map ((d + e) +_) u ≡ map ((e + d) +_) u
map-+-comm {d = d} {e} = map-cong λ x → cong (_+ x) (+-comm d e)

map-+∘+-comm : map (d +_) (map (e +_) u) ≡ map (e +_) (map (d +_) u)
map-+∘+-comm {d = d} {e = e} =
  sym map-+-assoc ; map-+-comm {e = e} ; map-+-assoc

zip : Trie a ρ × Trie b ρ → Trie (a × b) ρ
zip (1̇ , 1̇) = 1̇
zip (İ a , İ b) = İ (a , b)
zip (as₁ ▿ as₂ , bs₁ ▿ bs₂) = zip (as₁ , bs₁) ▿ zip (as₂ , bs₂)

zip⁻¹ : Trie (a × b) ρ → Trie a ρ × Trie b ρ
zip⁻¹ 1̇ = 1̇ , 1̇
zip⁻¹ (İ (a , b)) = İ a , İ b
zip⁻¹ (as ▿ bs) = let as₁ , as₂ = zip⁻¹ as
                      bs₁ , bs₂ = zip⁻¹ bs
                  in as₁ ▿ bs₁ , as₂ ▿ bs₂

-- Objects are time tries
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

-- Progressively delayed objects
Delays : 𝕋 → Obj → ℕ → Obj
Delays d A zero = ⊤
Delays d A (suc n) = A × Delay d (Delays d A n)

-- Morphisms are functions on bit tries
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

-- Apply timing identities
subT : ∀ {u v : Trie 𝕋 ρ} → v ≡ u → obj u ⇨ obj v
subT refl = id
-- subT v≡u = sub id (cong obj (sym v≡u))

-- V a zero = ⊤
-- V a (suc n) = a × V a n

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

-- Generalize pipe to mealy by adding a running accumulator ("state"):

-- Untimed
mealy′ : ∀ {s} → (s × a → b × s) → ∀ n → s × V a n → V b n × s
mealy′ h zero (s , tt) = tt , s
mealy′ h (suc n) (s , (a , as)) = let b  , t = h (s , a )
                                      bs , u = mealy′ h n (t , as)
                                  in (b , bs) , u

-- Categorical formulation
mealy″ : ∀ {s} → (s × a → b × s) → ∀ n → s × V a n → V b n × s
mealy″ h  zero   = unitorⁱˡ ∘ unitorᵉʳ
mealy″ h (suc n) = assocˡ ∘ second (mealy″ h n) ∘ inAssocˡ h

-- Timed
mealy : (S × A ⇨ B × Delay d S) →
  ∀ n → S × Delays d A n ⇨ Delays d B n × Delay (n * d) S
mealy h zero = unitorⁱˡ ∘ subT map-+-identityˡ ∘ unitorᵉʳ
mealy h (suc n) =
  assocˡ ∘ second (second (subT map-+-assoc) ∘ delay (mealy h n)) ∘ inAssocˡ h

-- The map-+-identityˡ lemma reconciles Delay (zero * d) S with S.

-- The map-+-assoc lemma reconciles Delay (suc n * d) (i.e., Delay (d + n * d)) with
-- Delay (d (Delay (n * d))).

-- The shape of morphism coming out of mealy matches the morphism shape coming
-- in, and thus mealy can be applied repeatedly, e.g., mealy (mealy (mealy h)).

-- More usefully, invert roles of input and state: mealy (swap ∘ mealy ∘ swap).

-- TODO: Generalize mealy to nonuniform timing (via prefix sums of timing).

-- pipe as mealy with empty state (S = ⊤)
pipeM : (A ⇨ B) → ∀ n → Delays d A n ⇨ Delays d B n
pipeM f n = unitorᵉʳ ∘ mealy (unitorⁱʳ ∘ f ∘ unitorᵉˡ) n ∘ unitorⁱˡ

scan : (B × A ⇨ Delay d B) →
  ∀ n → B × Delays d A n ⇨ Delays d (Delay d B) n × Delay (n * d) B
scan f = mealy (dup ∘ f)

fold : (B × A ⇨ Delay d B) → ∀ n → B × Delays d A n ⇨ Delay (n * d) B
fold f n = exr ∘ scan f n

-- TODO: Consistent naming scheme. Maybe mapD, scanD, foldD. Later, however,
-- we'll want *nonsequential* timed variants.

---- Examples


-- Gate delay
γ : 𝕋
γ = 2

⊕γ ∧γ : 𝔹 × 𝔹 ⇨ Delay γ 𝔹
⊕γ = delay ⊕ ∘ pause
∧γ = delay ∧ ∘ pause

-- ⊕γ = pause ∘ ⊕
-- ∧γ = pause ∘ ∧

-- Half adder with carry-out on right.
up₁ : 𝔹 × 𝔹 ⇨ Delay γ (𝔹 × 𝔹)
up₁ = ⊕γ ▵ ∧γ

-- Conditionally increment an n-bit natural number
up : ∀ n → 𝔹 × Delays γ 𝔹 n ⇨ Delays γ (Delay γ 𝔹) n × Delay (n * γ) 𝔹
up = mealy up₁

-- TODO: Try replacing V a n with Trie a (𝔽 n), where ⟦ 𝔽 n ⟧ ≅ Fin n.

𝔽 : ℕ → Shape
𝔽 zero = `⊥
𝔽 (suc n) = `⊤ `⊎ 𝔽 n

-- TODO: then consider generalizations from V to other tries.


-- Delays-Delay : ∀ n → Delays d (Delay e A) n ≡ Delay e (Delays d A n)
Delays-Delay : ∀ n → Delays d (Delay e A) n ≡ Delay e (Delays d A n)
Delays-Delay zero = refl
Delays-Delay {d} {e} {A} (suc n) =
  begin
    Delays d (Delay e A) (suc n)
  ≡⟨⟩
    (Delay e A × Delay d (Delays d (Delay e A) n))
  ≡⟨ cong (λ ● → Delay e A × Delay d ●) (Delays-Delay n) ⟩
    (Delay e A × Delay d (Delay e (Delays d A n)))
  ≡⟨ cong (Delay e A ×_) (cong obj map-+∘+-comm) ⟩
    (Delay e A × Delay e (Delay d (Delays d A n)))
  ≡⟨⟩
    Delay e (A × Delay d (Delays d A n))
  ≡⟨⟩
    Delay e (Delays d A (suc n))
  ∎
 where open ≡-Reasoning

zipD : ∀ n → Delays d A n × Delays d B n ⇨ Delays d (A × B) n
zipD zero = unitorᵉˡ
zipD (suc n) = second (delay (zipD n)) ∘ transpose

zipD⁻¹ : ∀ n → Delays d (A × B) n ⇨ Delays d A n × Delays d B n
zipD⁻¹ zero = unitorⁱˡ
zipD⁻¹ (suc n) = transpose ∘ second (delay (zipD⁻¹ n))

-- Note that zipD & zipD⁻¹ form an isomorphism


---- Experiments in nested (higher-dimensional?) mealy machines

mealy²₁ : (S × A ⇨ B × Delay d S) → ∀ m n →
  S × Delays (m * d) (Delays d A m) n ⇨
    Delays (m * d) (Delays d B m) n × Delay (n * (m * d)) S
mealy²₁ h m n = mealy (mealy h m) n

up² : ∀ m n →
  𝔹 × Delays (m * γ) (Delays γ 𝔹 m) n ⇨
    Delays (m * γ) (Delays γ (Delay γ 𝔹) m) n × Delay (n * (m * γ)) 𝔹
up² = mealy²₁ up₁

private module Foo (h : S × A ⇨ Delay e A × Delay d S) n where

  foo₁ : S × Delays d A n ⇨ Delays d (Delay e A) n × Delay (n * d) S
  foo₁ = mealy h n

  foo₂ : Delays d A n × S ⇨ Delay (n * d) S × Delays d (Delay e A) n
  foo₂ = swap ∘ mealy h n ∘ swap

  foo₃ : Delays d A n × S ⇨ Delay (n * d) S × Delay e (Delays d A n)
  foo₃ = second (sub≡ (Delays-Delay n)) ∘ swap ∘ mealy h n ∘ swap

  foo₄ : ∀ m → Delays d A n × Delays e S m ⇨
           Delays e (Delay (n * d) S) m × Delay (m * e) (Delays d A n)
  foo₄ = mealy foo₃

  foo₅ : ∀ m → Delays d A n × Delays e S m ⇨
           Delay (n * d) (Delays e S m) × Delay (m * e) (Delays d A n)
  foo₅ m = first (sub≡ (Delays-Delay m)) ∘ foo₄ m

mealy²₂ : (h : S × A ⇨ Delay e A × Delay d S) → ∀ m n →
  Delays d A m × Delays e S n ⇨
     Delay (m * d) (Delays e S n) × Delay (n * e) (Delays d A m)
mealy²₂ h m n = first (sub≡ (Delays-Delay n)) ∘
            mealy (second (sub≡ (Delays-Delay m)) ∘ swap ∘ mealy h m ∘ swap) n

counter₁ : ∀ n → Delays γ 𝔹 n × Delays γ 𝔹 n ⇨
  -- Delay (n * γ) (Delays γ 𝔹 n) × Delay (n * γ) (Delays γ 𝔹 n)
  Delay (n * γ) (Delays γ 𝔹 n × Delays γ 𝔹 n)
counter₁ n = mealy²₂ up₁ n n

-- counter₁ takes an initial count and carries-in and yields carries-out and a
-- final count.

-- A prettier formulation:
counter₂ : ∀ n → Delays γ (𝔹 × 𝔹) n ⇨ Delay (n * γ) (Delays γ (𝔹 × 𝔹) n)
counter₂ n = delay (zipD n) ∘ counter₁ n ∘ zipD⁻¹ n

