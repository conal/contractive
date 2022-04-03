-- A category of spacetime-located computation. Objects are (spacetime)-location
-- tries, and morphisms are computable functions between bit tries (easily
-- generalized to arbitrary atomic types). The relationship to regular
-- computable functions is a simple functor that forgets times. Later, we'll
-- swap out functions (denotation) for a compilable representation, again with a
-- functor back to semantics. As always, implementation correctness is semantic
-- homomorphicity/functoriality.

-- "Spacetime" is meant to be suggestive here but can be any commutative monoid.
-- Most operations don't even need commutativity, and I could localize that
-- assumption to where it's used.

-- TODO: consider coproducts. What are timing structures for sums? Normally I
-- don't think of sum types as tries, but they're probably *dependent* tries.

open import Level using (Level; 0ℓ)
open import Relation.Binary.PropositionalEquality as ≡
open import Algebra.Core using (Op₂)
import Algebra.Structures as AS

module Spacetime {𝕊 : Set} (open AS {A = 𝕊} _≡_)
   (_+′_ : Op₂ 𝕊) (let infixl 6 _+_; _+_ = _+′_) (ε : 𝕊)
   (isCommutativeMonoid : IsCommutativeMonoid _+_ ε)
 where

open import Algebra.Bundles using (Monoid)

open IsCommutativeMonoid isCommutativeMonoid hiding (refl; trans; sym)

monoid : Monoid 0ℓ 0ℓ
monoid = record { isMonoid = isMonoid}

-- For now, require equality. If we generalize, then take commutativeMonoid as a
-- module parameter.

open import Algebra.Properties.Monoid.Mult (monoid) renaming (_×_ to _·_)

open import Data.Empty.Polymorphic
open import Data.Sum using (_⊎_)
open import Data.Nat renaming (_+_ to _✢_)
open import Data.Nat.Properties
open import Data.Product using (_,_)

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
size (ρ `⊎ σ) = size ρ ✢ size σ

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

private variable m n : ℕ ; s t d e : 𝕊

·-distrib-+ʳ : ∀ m → (m ✢ n) · d ≡ m · d + n · d
·-distrib-+ʳ zero = sym (identityˡ _)
·-distrib-+ʳ {n} {d} (suc m) =
  begin
    (suc m ✢ n) · d
  ≡⟨⟩
    d + (m ✢ n) · d
  ≡⟨ cong (d +_) (·-distrib-+ʳ m) ⟩
    (d + (m · d + n · d))
  ≡⟨ sym (assoc _ _ _) ⟩
    ((d + m · d) + n · d)
  ≡⟨⟩
    (suc m · d + n · d)
  ∎ where open ≡-Reasoning

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

-- TODO: Drop "+" from these names

map-identityˡ : ∀ ρ {u : Trie 𝕊 ρ} → map (ε +_) ρ u ≡ u
map-identityˡ ρ = map-cong identityˡ ρ ; map-id ρ

map-identityʳ : ∀ ρ {u : Trie 𝕊 ρ} → map (_+ ε) ρ u ≡ u
map-identityʳ ρ = map-cong identityʳ ρ ; map-id ρ

map-1· : ∀ ρ {u : Trie 𝕊 ρ} → map (1 · d +_) ρ u ≡ map (d +_) ρ u
map-1· {d} = map-cong (λ x → cong (_+ x) (identityʳ d))

map-assoc : ∀ ρ {u : Trie 𝕊 ρ} →
  map ((d + e) +_) ρ u ≡ map (d +_) ρ (map (e +_) ρ u)
map-assoc {d = d} {e} ρ = map-cong (assoc d e) ρ ; map-∘ ρ

map-comm : ∀ ρ {u : Trie 𝕊 ρ} → map ((d + e) +_) ρ u ≡ map ((e + d) +_) ρ u
map-comm {d = d} {e} = map-cong (λ x → cong (_+ x) (comm d e))

map-+∘+-comm : ∀ ρ {u : Trie 𝕊 ρ} →
  map (d +_) ρ (map (e +_) ρ u) ≡ map (e +_) ρ (map (d +_) ρ u)
map-+∘+-comm {d = d} {e = e} ρ =
  sym (map-assoc ρ) ; map-comm {e = e} ρ ; map-assoc ρ

map-distribʳ : ∀ ρ {u : Trie 𝕊 ρ} → ∀ m →
  map ((m ✢ n) · d +_) ρ u ≡ map (m · d + n · d +_) ρ u
map-distribʳ ρ m = map-cong (λ x → cong (_+ x) (·-distrib-+ʳ m)) ρ

map-distribʳ-assoc : ∀ ρ {u : Trie 𝕊 ρ} → ∀ m →
  map ((m ✢ n) · d +_) ρ u ≡ map (m · d +_) ρ (map (n · d +_) ρ u)
map-distribʳ-assoc ρ m = map-distribʳ ρ m ; map-assoc ρ

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
    times : Trie 𝕊 shape
open Obj public

private variable A B C D S : Obj

module timed-obj-instances where instance

  products : Products Obj
  products = record
    { ⊤ = obj `⊥ tt
    ; _×_ = λ (obj ρ u) (obj σ v) → obj (ρ `⊎ σ) (u , v)
    }

  boolean : Boolean Obj
  boolean = record { Bool = obj `⊤ ε }

Relocate : (h : 𝕊 → 𝕊) → Obj → Obj
Relocate h (obj ρ ts) = obj ρ (map h ρ ts)

Move : 𝕊 → Obj → Obj
Move d = Relocate (d +_)

infixl 7 _·̂_
_·̂_ : Shape → 𝕊 → 𝕊
ρ ·̂ d = size ρ · d

-- Progressively moveed rightward traversal
Moves : 𝕊 → Obj → Shape → Obj
Moves d A `⊥ = ⊤
Moves d A `⊤ = A
Moves d A (ρ `⊎ σ) = Moves d A ρ × Move (ρ ·̂ d) (Moves d A σ)

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

relocate : ∀ {g h} → (A ⇨ B) → (Relocate g A ⇨ Relocate h B)
relocate (mk f) = mk f

move : (A ⇨ B) → (Move d A ⇨ Move d B)
move = relocate
-- move (mk f) = mk f

-- Note: Move d and move form a cartesian (endo)functor.

shift : A ⇨ Move d A
shift = mk id

-- Apply timing identities
subT : ∀ {u v : Trie 𝕊 ρ} → v ≡ u → obj ρ u ⇨ obj ρ v
subT refl = id
-- subT v≡u = sub id (cong obj (sym v≡u))

-- Temporal version. First version.
mapT₁ : ∀ (f : A ⇨ B) ρ → Moves d A ρ ⇨ Moves d B ρ
mapT₁ f `⊥ = !
mapT₁ f `⊤ = f
mapT₁ f (ρ `⊎ σ) = mapT₁ f ρ ⊗ move (mapT₁ f σ)

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
mealy : ∀ (h : S × A ⇨ B × Move d S) ρ →
  S × Moves d A ρ ⇨ Moves d B ρ × Move (ρ ·̂ d) S
mealy {S} h `⊥ = unitorⁱˡ ∘ subT (map-identityˡ (shape S)) ∘ unitorᵉʳ
mealy {S} h `⊤ = second (subT (map-1· (shape S))) ∘ h
mealy {S} h (ρ `⊎ σ) =
  assocˡ ∘
  second (second (subT (map-distribʳ-assoc (shape S) (size ρ))) ∘
          move (mealy h σ)) ∘
  inAssocˡ (mealy h ρ)

-- The shape of morphism coming out of mealy matches the morphism shape coming
-- in, and thus mealy can be applied repeatedly, e.g., mealy (mealy (mealy h)).
-- More usefully, invert roles of input and state: mealy (swap ∘ mealy ∘ swap).
-- See below.

-- TODO: Generalize mealy to nonuniform timing (via prefix sums of timing).

-- mapM as mealyS with empty state (S = ⊤)
mapM : ∀ (f : A ⇨ B) ρ → Moves d A ρ ⇨ Moves d B ρ
mapM f ρ = unitorᵉʳ ∘ mealy (unitorⁱʳ ∘ f ∘ unitorᵉˡ) ρ ∘ unitorⁱˡ

scan : ∀ (f : B × A ⇨ Move d B) ρ →
  B × Moves d A ρ ⇨ Moves d (Move d B) ρ × Move (ρ ·̂ d) B
scan f = mealy (dup ∘ f)

fold : ∀ (f : B × A ⇨ Move d B) ρ → B × Moves d A ρ ⇨ Move (ρ ·̂ d) B
fold f ρ = exr ∘ scan f ρ

-- TODO: Consistent naming scheme. Maybe mapD, scanD, foldD. Later, however,
-- we'll want ·nonsequential· timed variants.

-- Moves-Move : ∀ n → Moves d (Move e A) n ≡ Move e (Moves d A n)
Moves-Move : ∀ ρ → Moves d (Move e A) ρ ≡ Move e (Moves d A ρ)
Moves-Move `⊥ = refl
Moves-Move `⊤ = refl
Moves-Move {d} {e} {A} (ρ `⊎ σ) =
  begin
    Moves d (Move e A) (ρ `⊎ σ)
  ≡⟨⟩
    (Moves d (Move e A) ρ × Move (ρ ·̂ d) (Moves d (Move e A) σ))
  ≡⟨ cong₂ (λ ● ○ → ● × Move (ρ ·̂ d) ○)
           (Moves-Move ρ) (Moves-Move σ) ⟩
    (Move e (Moves d A ρ) × Move (ρ ·̂ d) (Move e (Moves d A σ)))
  ≡⟨ cong (Move e (Moves d A ρ) ×_) (cong (obj σ·) (map-+∘+-comm σ·)) ⟩
    (Move e (Moves d A ρ) × Move e (Move (ρ ·̂ d) (Moves d A σ)))
  ≡⟨⟩
    Move e (Moves d A ρ × Move (ρ ·̂ d) (Moves d A σ))
  ≡⟨⟩
    Move e (Moves d A (ρ `⊎ σ))
  ∎
 where σ· = shape (Moves d A σ)
       open ≡-Reasoning

zipM : ∀ ρ → Moves d A ρ × Moves d B ρ ⇨ Moves d (A × B) ρ
zipM `⊥ = unitorᵉˡ
zipM `⊤ = id
zipM (ρ `⊎ σ) = (zipM ρ ⊗ move (zipM σ)) ∘ transpose

zipM⁻¹ : ∀ ρ → Moves d (A × B) ρ ⇨ Moves d A ρ × Moves d B ρ
zipM⁻¹ `⊥ = unitorⁱˡ
zipM⁻¹ `⊤ = id
zipM⁻¹ (ρ `⊎ σ) = transpose ∘ (zipM⁻¹ ρ ⊗ move (zipM⁻¹ σ))

-- Note that zipM & zipM⁻¹ form an isomorphism


---- Experiments in nested (higher-dimensional?) mealy machines

-- Here's where we use commutativity of +:
mealy²₁ : ∀ (h : S × A ⇨ B × Move d S) ρ σ →
  S × Moves (ρ ·̂ d) (Moves d A ρ) σ ⇨
    Moves (ρ ·̂ d) (Moves d B ρ) σ × Move (σ ·̂ (ρ ·̂ d)) S
mealy²₁ h ρ σ = mealy (mealy h ρ) σ

private module Foo (h : S × A ⇨ Move e A × Move d S) σ where

  foo₁ : S × Moves d A σ ⇨ Moves d (Move e A) σ × Move (σ ·̂ d) S
  foo₁ = mealy h σ

  foo₂ : Moves d A σ × S ⇨ Move (σ ·̂ d) S × Moves d (Move e A) σ
  foo₂ = swap ∘ mealy h σ ∘ swap

  foo₃ : Moves d A σ × S ⇨ Move (σ ·̂ d) S × Move e (Moves d A σ)
  foo₃ = second (sub≡ (Moves-Move σ)) ∘ swap ∘ mealy h σ ∘ swap

  foo₄ : ∀ ρ → Moves d A σ × Moves e S ρ ⇨
           Moves e (Move (σ ·̂ d) S) ρ × Move (ρ ·̂ e) (Moves d A σ)
  foo₄ ρ = mealy foo₃ ρ

  foo₅ : ∀ ρ → Moves d A σ × Moves e S ρ ⇨
           Move (σ ·̂ d) (Moves e S ρ) × Move (ρ ·̂ e) (Moves d A σ)
  foo₅ ρ = first (sub≡ (Moves-Move ρ)) ∘ foo₄ ρ

mealy²₂ : (h : S × A ⇨ Move e A × Move d S) → ∀ ρ σ →
  Moves d A ρ × Moves e S σ ⇨
     Move (ρ ·̂ d) (Moves e S σ) × Move (σ ·̂ e) (Moves d A ρ)
mealy²₂ h ρ σ = first (sub≡ (Moves-Move σ)) ∘
            mealy (second (sub≡ (Moves-Move ρ)) ∘ swap ∘ mealy h ρ ∘ swap) σ


-- Parametrize over spacetime offset for ⊕ and ∧ gates
module Examples (γ : 𝕊) where

  ⊕γ ∧γ : 𝔹 × 𝔹 ⇨ Move γ 𝔹
  ⊕γ = move ⊕ ∘ shift
  ∧γ = move ∧ ∘ shift

  -- ⊕γ = shift ∘ ⊕
  -- ∧γ = shift ∘ ∧

  -- Half adder with carry-out on right.
  up₁ : 𝔹 × 𝔹 ⇨ Move γ (𝔹 × 𝔹)
  up₁ = ⊕γ ▵ ∧γ

  -- Conditionally increment an n-bit natural number
  up : ∀ ρ → 𝔹 × Moves γ 𝔹 ρ ⇨ Moves γ (Move γ 𝔹) ρ × Move (ρ ·̂ γ) 𝔹
  up = mealy up₁

  up² : ∀ ρ σ →
    𝔹 × Moves (ρ ·̂ γ) (Moves γ 𝔹 ρ) σ ⇨
      Moves (ρ ·̂ γ) (Moves γ (Move γ 𝔹) ρ) σ × Move (σ ·̂ (ρ ·̂ γ)) 𝔹
  up² = mealy²₁ up₁

  counter : ∀ ρ σ →
    Moves γ 𝔹 ρ × Moves γ 𝔹 σ ⇨
      Move (ρ ·̂ γ) (Moves γ 𝔹 σ) × Move (σ ·̂ γ) (Moves γ 𝔹 ρ)
  counter = mealy²₂ up₁

  -- counter takes a ρ-bit initial count and σ carries-in and yields σ
  -- carries-out and a final ρ-bit count. Note the lovely symmetry in the type.

-- TODO: Write up notes, including untimed versions of mealy²₁ and mealy²₂ (and
-- choose better names).
