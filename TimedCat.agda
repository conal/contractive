-- A category of timed computation. Objects are time tries, and morphisms are
-- computable functions between bit tries (easily generalized to arbitrary
-- atomic types). The relationship to regular computable functions is a simple
-- functor that forgets times. Later, we'll swap out functions (denotation) for
-- a compilable representation, again with a functor back to semantics. As
-- always, implementation correctness is semantic homomorphicity/functoriality.

-- TODO: consider coproducts. What are timing structures for sums? Normally I
-- don't think of sum types as tries, but they're probably *dependent* tries.

module TimedCat where

open import Level using (Level; 0ℓ)
open import Data.Empty.Polymorphic
open import Data.Sum using (_⊎_)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality as ≡

open import Categorical.Raw renaming (xor to ⊕; Bool to 𝔹)
open import Functions 0ℓ

private variable
  ℓ o : Level
  a b c : Set

infixr 1 _;_   -- unicode
_;_ : ∀ {a : Set ℓ} {x y z : a} → x ≡ y → y ≡ z → x ≡ z
_;_ = trans

infixr 6 _`⊎_
data Shape : Set where
  `⊥ : Shape
  `⊤ : Shape
  _`⊎_  : (ρ σ : Shape) → Shape

private variable ρ σ : Shape

size : Shape → ℕ
size `⊥ = 0
size `⊤ = 1
size (ρ `⊎ σ) = size ρ + size σ

⟦_⟧ : Shape → Set
⟦ `⊥ ⟧ = ⊥
⟦ `⊤ ⟧ = ⊤
⟦ ρ `⊎ σ ⟧ = ⟦ ρ ⟧ ⊎ ⟦ σ ⟧

𝔽 : ℕ → Shape
𝔽 zero = `⊥
𝔽 (suc n) = `⊤ `⊎ 𝔽 n

Trie : {obj : Set o} ⦃ _ : Products obj ⦄ → obj → Shape → obj
Trie a `⊥ = ⊤
Trie a `⊤ = a
Trie a (ρ `⊎ σ) = Trie a ρ × Trie a σ

-- Trie a ρ ≅ ⟦ ρ ⟧ → a

private variable u v : Trie a ρ

-- "Time", which could be ℚ, ℝ, or an arbitrary commutative monoid such as
-- spacetime.
𝕋 : Set
𝕋 = ℕ

private variable m n : ℕ ; s t d e : 𝕋

map : (a → b) → ∀ ρ → Trie a ρ → Trie b ρ
map f `⊥ = !
map f `⊤ = f
map f (ρ `⊎ σ) = map f ρ ⊗ map f σ

map-id : ∀ ρ {u : Trie a ρ} → map id ρ u ≡ u
map-id `⊥ = refl
map-id `⊤ = refl
map-id (ρ `⊎ σ) = cong₂ _,_ (map-id ρ) (map-id σ)

map-∘ : ∀ ρ {f : a → b} {g : b → c} {u : Trie a ρ} → map (g ∘ f) ρ u ≡ map g ρ (map f ρ u)
map-∘ `⊥ = refl
map-∘ `⊤ = refl
map-∘ (ρ `⊎ σ) = cong₂ _,_ (map-∘ ρ) (map-∘ σ)

map-cong : ∀ {f g : a → b} → f ≗ g → ∀ ρ {u : Trie a ρ} → map f ρ u ≡ map g ρ u
map-cong f≗g `⊥ = refl
map-cong f≗g `⊤ = f≗g _
map-cong f≗g (ρ `⊎ σ) = cong₂ _,_ (map-cong f≗g ρ) (map-cong f≗g σ)

-- Corollaries

map-+-identityˡ : ∀ ρ {u : Trie 𝕋 ρ} → map (0 +_) ρ u ≡ u
map-+-identityˡ = map-id

map-+-identityʳ : ∀ ρ {u : Trie 𝕋 ρ} → map (_+ 0) ρ u ≡ u
map-+-identityʳ ρ = map-cong +-identityʳ ρ ; map-id ρ

map-+-1* : ∀ ρ {u : Trie 𝕋 ρ} → map (1 * d +_) ρ u ≡ map (d +_) ρ u
map-+-1* {d} = map-cong (λ x → cong (_+ x) (+-identityʳ d))

map-+-assoc : ∀ ρ {u : Trie 𝕋 ρ} →
  map ((d + e) +_) ρ u ≡ map (d +_) ρ (map (e +_) ρ u)
map-+-assoc {d = d} {e} ρ = map-cong (+-assoc d e) ρ ; map-∘ ρ

map-+-comm : ∀ ρ {u : Trie 𝕋 ρ} → map ((d + e) +_) ρ u ≡ map ((e + d) +_) ρ u
map-+-comm {d = d} {e} = map-cong (λ x → cong (_+ x) (+-comm d e))

map-+∘+-comm : ∀ ρ {u : Trie 𝕋 ρ} →
  map (d +_) ρ (map (e +_) ρ u) ≡ map (e +_) ρ (map (d +_) ρ u)
map-+∘+-comm {d = d} {e = e} ρ =
  sym (map-+-assoc ρ) ; map-+-comm {e = e} ρ ; map-+-assoc ρ

map-+-distribʳ : ∀ ρ {u : Trie 𝕋 ρ} → ∀ m →
  map ((m + n) * d +_) ρ u ≡ map (m * d + n * d +_) ρ u
map-+-distribʳ ρ m = map-cong (λ x → cong (_+ x) (*-distribʳ-+ _ m _)) ρ

map-+-distribʳ-assoc : ∀ ρ {u : Trie 𝕋 ρ} → ∀ m →
  map ((m + n) * d +_) ρ u ≡ map (m * d +_) ρ (map (n * d +_) ρ u)
map-+-distribʳ-assoc ρ m = map-+-distribʳ ρ m ; map-+-assoc ρ

zip : ∀ ρ → Trie a ρ × Trie b ρ → Trie (a × b) ρ
zip `⊥ = unitorᵉʳ
zip `⊤ = id
zip (ρ `⊎ σ) = (zip ρ ⊗ zip σ) ∘ transpose

zip⁻¹ : ∀ ρ → Trie (a × b) ρ → Trie a ρ × Trie b ρ
zip⁻¹ `⊥ = unitorⁱʳ
zip⁻¹ `⊤ = id
zip⁻¹ (ρ `⊎ σ) = transpose ∘ (zip⁻¹ ρ ⊗ zip⁻¹ σ)


-- Objects are time tries
record Obj : Set where
  constructor obj
  field
    shape : Shape
    times : Trie 𝕋 shape
open Obj public

private variable A B C D S : Obj

module timed-obj-instances where instance

  products : Products Obj
  products = record
    { ⊤ = obj `⊥ tt
    ; _×_ = λ (obj ρ u) (obj σ v) → obj (ρ `⊎ σ) (u , v)
    }

  boolean : Boolean Obj
  boolean = record { Bool = obj `⊤ 0 }

Retime : (h : 𝕋 → 𝕋) → Obj → Obj
Retime h (obj ρ ts) = obj ρ (map h ρ ts)

Delay : 𝕋 → Obj → Obj
Delay d = Retime (d +_)

infixl 7 _*̂_
_*̂_ : Shape → 𝕋 → 𝕋
ρ *̂ d = size ρ * d

-- Progressively delayed rightward traversal
Delays : 𝕋 → Obj → Shape → Obj
Delays d A `⊥ = ⊤
Delays d A `⊤ = A
Delays d A (ρ `⊎ σ) = Delays d A ρ × Delay (ρ *̂ d) (Delays d A σ)

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
    {  !  = mk !
    ; _▵_ = λ (mk f) (mk g) → mk (f ▵ g)
    ; exl = mk exl
    ; exr = mk exr
    }

  logic : Logic _⇨_
  logic = record
    { false = mk false
    ; true  = mk true
    ; not   = mk not
    ; ∧     = mk ∧ 
    ; ∨     = mk ∨
    ; xor   = mk ⊕
    ; cond  = mk cond
    }

-- TODO: Define via Subcategory

retime : ∀ {g h} → (A ⇨ B) → (Retime g A ⇨ Retime h B)
retime (mk f) = mk f

delay : (A ⇨ B) → (Delay d A ⇨ Delay d B)
delay = retime
-- delay (mk f) = mk f

-- Note: Delay d and delay form a cartesian (endo)functor.

pause : A ⇨ Delay d A
pause = mk id

-- Apply timing identities
subT : ∀ {u v : Trie 𝕋 ρ} → v ≡ u → obj ρ u ⇨ obj ρ v
subT refl = id
-- subT v≡u = sub id (cong obj (sym v≡u))

-- Temporal version. First version.
mapT₁ : ∀ (f : A ⇨ B) ρ → Delays d A ρ ⇨ Delays d B ρ
mapT₁ f `⊥ = !
mapT₁ f `⊤ = f
mapT₁ f (ρ `⊎ σ) = mapT₁ f ρ ⊗ delay (mapT₁ f σ)

-- Generalize mapT to mealyT by adding a running accumulator ("state"):

-- Untimed
mealy′ : ∀ {s} (h : s × a → b × s) ρ → s × Trie a ρ → Trie b ρ × s
mealy′ h `⊥ (x , tt) = tt , x
mealy′ h `⊤ (s , x) = h (s , x)
mealy′ h (ρ `⊎ σ) (s , (xs₁ , xs₂)) =
  let ys₁ , t₁ = mealy′ h ρ (s  , xs₁)
      ys₂ , t₂ = mealy′ h σ (t₁ , xs₂)
  in (ys₁ , ys₂) , t₂

-- Categorical formulation
mealy″ : ∀ {s} (h : s × a → b × s) ρ → s × Trie a ρ → Trie b ρ × s
mealy″ h `⊥ = unitorⁱˡ ∘ unitorᵉʳ -- swap
mealy″ h `⊤ = h
mealy″ h (ρ `⊎ σ) = assocˡ ∘ second (mealy″ h σ) ∘ inAssocˡ (mealy″ h ρ)

-- Categorical formulation
mealy : ∀ (h : S × A ⇨ B × Delay d S) ρ →
  S × Delays d A ρ ⇨ Delays d B ρ × Delay (ρ *̂ d) S
mealy {S} h `⊥ = unitorⁱˡ ∘ subT (map-+-identityˡ (shape S)) ∘ unitorᵉʳ
mealy {S} h `⊤ = second (subT (map-+-1* (shape S))) ∘ h
mealy {S} h (ρ `⊎ σ) =
  assocˡ ∘
  second (second (subT (map-+-distribʳ-assoc (shape S) (size ρ))) ∘
          delay (mealy h σ)) ∘
  inAssocˡ (mealy h ρ)

-- The shape of morphism coming out of mealy matches the morphism shape coming
-- in, and thus mealy can be applied repeatedly, e.g., mealy (mealy (mealy h)).
-- More usefully, invert roles of input and state: mealy (swap ∘ mealy ∘ swap).
-- See below.

-- TODO: Generalize mealy to nonuniform timing (via prefix sums of timing).

-- mapT as mealyS with empty state (S = ⊤)
mapT : ∀ (f : A ⇨ B) ρ → Delays d A ρ ⇨ Delays d B ρ
mapT f ρ = unitorᵉʳ ∘ mealy (unitorⁱʳ ∘ f ∘ unitorᵉˡ) ρ ∘ unitorⁱˡ

scan : ∀ (f : B × A ⇨ Delay d B) ρ →
  B × Delays d A ρ ⇨ Delays d (Delay d B) ρ × Delay (ρ *̂ d) B
scan f = mealy (dup ∘ f)

fold : ∀ (f : B × A ⇨ Delay d B) ρ → B × Delays d A ρ ⇨ Delay (ρ *̂ d) B
fold f ρ = exr ∘ scan f ρ

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
up : ∀ ρ → 𝔹 × Delays γ 𝔹 ρ ⇨ Delays γ (Delay γ 𝔹) ρ × Delay (ρ *̂ γ) 𝔹
up = mealy up₁

-- Delays-Delay : ∀ n → Delays d (Delay e A) n ≡ Delay e (Delays d A n)
Delays-Delay : ∀ ρ → Delays d (Delay e A) ρ ≡ Delay e (Delays d A ρ)
Delays-Delay `⊥ = refl
Delays-Delay `⊤ = refl
Delays-Delay {d} {e} {A} (ρ `⊎ σ) =
  begin
    Delays d (Delay e A) (ρ `⊎ σ)
  ≡⟨⟩
    (Delays d (Delay e A) ρ × Delay (ρ *̂ d) (Delays d (Delay e A) σ))
  ≡⟨ cong₂ (λ ● ○ → ● × Delay (ρ *̂ d) ○)
           (Delays-Delay ρ) (Delays-Delay σ) ⟩
    (Delay e (Delays d A ρ) × Delay (ρ *̂ d) (Delay e (Delays d A σ)))
  ≡⟨ cong (Delay e (Delays d A ρ) ×_) (cong (obj σ*) (map-+∘+-comm σ*)) ⟩
    (Delay e (Delays d A ρ) × Delay e (Delay (ρ *̂ d) (Delays d A σ)))
  ≡⟨⟩
    Delay e (Delays d A ρ × Delay (ρ *̂ d) (Delays d A σ))
  ≡⟨⟩
    Delay e (Delays d A (ρ `⊎ σ))
  ∎
 where σ* = shape (Delays d A σ)
       open ≡-Reasoning

zipD : ∀ ρ → Delays d A ρ × Delays d B ρ ⇨ Delays d (A × B) ρ
zipD `⊥ = unitorᵉˡ
zipD `⊤ = id
zipD (ρ `⊎ σ) = (zipD ρ ⊗ delay (zipD σ)) ∘ transpose

zipD⁻¹ : ∀ ρ → Delays d (A × B) ρ ⇨ Delays d A ρ × Delays d B ρ
zipD⁻¹ `⊥ = unitorⁱˡ
zipD⁻¹ `⊤ = id
zipD⁻¹ (ρ `⊎ σ) = transpose ∘ (zipD⁻¹ ρ ⊗ delay (zipD⁻¹ σ))

-- Note that zipD & zipD⁻¹ form an isomorphism


---- Experiments in nested (higher-dimensional?) mealy machines

mealy²₁ : ∀ (h : S × A ⇨ B × Delay d S) ρ σ →
  S × Delays (ρ *̂ d) (Delays d A ρ) σ ⇨
    Delays (ρ *̂ d) (Delays d B ρ) σ × Delay (σ *̂ (ρ *̂ d)) S
mealy²₁ h ρ σ = mealy (mealy h ρ) σ

up² : ∀ ρ σ →
  𝔹 × Delays (ρ *̂ γ) (Delays γ 𝔹 ρ) σ ⇨
    Delays (ρ *̂ γ) (Delays γ (Delay γ 𝔹) ρ) σ × Delay (σ *̂ (ρ *̂ γ)) 𝔹
up² = mealy²₁ up₁

private module Foo (h : S × A ⇨ Delay e A × Delay d S) σ where

  foo₁ : S × Delays d A σ ⇨ Delays d (Delay e A) σ × Delay (σ *̂ d) S
  foo₁ = mealy h σ

  foo₂ : Delays d A σ × S ⇨ Delay (σ *̂ d) S × Delays d (Delay e A) σ
  foo₂ = swap ∘ mealy h σ ∘ swap

  foo₃ : Delays d A σ × S ⇨ Delay (σ *̂ d) S × Delay e (Delays d A σ)
  foo₃ = second (sub≡ (Delays-Delay σ)) ∘ swap ∘ mealy h σ ∘ swap

  foo₄ : ∀ ρ → Delays d A σ × Delays e S ρ ⇨
           Delays e (Delay (σ *̂ d) S) ρ × Delay (ρ *̂ e) (Delays d A σ)
  foo₄ ρ = mealy foo₃ ρ

  foo₅ : ∀ ρ → Delays d A σ × Delays e S ρ ⇨
           Delay (σ *̂ d) (Delays e S ρ) × Delay (ρ *̂ e) (Delays d A σ)
  foo₅ ρ = first (sub≡ (Delays-Delay ρ)) ∘ foo₄ ρ

mealy²₂ : (h : S × A ⇨ Delay e A × Delay d S) → ∀ ρ σ →
  Delays d A ρ × Delays e S σ ⇨
     Delay (ρ *̂ d) (Delays e S σ) × Delay (σ *̂ e) (Delays d A ρ)
mealy²₂ h ρ σ = first (sub≡ (Delays-Delay σ)) ∘
            mealy (second (sub≡ (Delays-Delay ρ)) ∘ swap ∘ mealy h ρ ∘ swap) σ

counter : ∀ ρ σ →
  Delays γ 𝔹 ρ × Delays γ 𝔹 σ ⇨
    Delay (ρ *̂ γ) (Delays γ 𝔹 σ) × Delay (σ *̂ γ) (Delays γ 𝔹 ρ)
counter = mealy²₂ up₁

-- counter takes a ρ-bit initial count and σ carries-in and yields σ
-- carries-out and a final ρ-bit count. Note the lovely symmetry in the type.

-- TODO: Write up notes, including untimed versions of mealy²₁ and mealy²₂ (and
-- choose better names).
