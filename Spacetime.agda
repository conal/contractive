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

open import Level using (Level; 0โ)
open import Relation.Binary.PropositionalEquality as โก
open import Algebra.Core using (Opโ)
import Algebra.Structures as AS

module Spacetime {๐ : Set} (open AS {A = ๐} _โก_)
   (_+โฒ_ : Opโ ๐) (let infixl 6 _+_; _+_ = _+โฒ_) (ฮต : ๐)
   (isCommutativeMonoid : IsCommutativeMonoid _+_ ฮต)
 where

open import Algebra.Bundles using (Monoid)

open IsCommutativeMonoid isCommutativeMonoid hiding (refl; trans; sym)

monoid : Monoid 0โ 0โ
monoid = record { isMonoid = isMonoid}

-- For now, require equality. If we generalize, then take commutativeMonoid as a
-- module parameter.

open import Algebra.Properties.Monoid.Mult (monoid) renaming (_ร_ to _ยท_)

open import Data.Empty.Polymorphic
open import Data.Sum using (_โ_)
open import Data.Nat renaming (_+_ to _โข_)
open import Data.Nat.Properties
open import Data.Product using (_,_)

open import Categorical.Raw renaming (xor to โ; Bool to ๐น)
open import Functions 0โ

private variable
  โ o : Level
  a b c : Set

infixr 1 _อพ_   -- unicode
_อพ_ : โ {a : Set โ} {x y z : a} โ x โก y โ y โก z โ x โก z
_อพ_ = trans

infixr 6 _`โ_
data Shape : Set where
  `โฅ : Shape
  `โค : Shape
  _`โ_  : (ฯ ฯ : Shape) โ Shape

private variable ฯ ฯ : Shape

size : Shape โ โ
size `โฅ = 0
size `โค = 1
size (ฯ `โ ฯ) = size ฯ โข size ฯ

โฆ_โง : Shape โ Set
โฆ `โฅ โง = โฅ
โฆ `โค โง = โค
โฆ ฯ `โ ฯ โง = โฆ ฯ โง โ โฆ ฯ โง

๐ฝ : โ โ Shape
๐ฝ zero = `โฅ
๐ฝ (suc n) = `โค `โ ๐ฝ n

Trie : {obj : Set o} โฆ _ : Products obj โฆ โ obj โ Shape โ obj
Trie a `โฅ = โค
Trie a `โค = a
Trie a (ฯ `โ ฯ) = Trie a ฯ ร Trie a ฯ

-- Trie a ฯ โ โฆ ฯ โง โ a

private variable u v : Trie a ฯ

private variable m n : โ ; s t d e : ๐

ยท-distrib-+สณ : โ m โ (m โข n) ยท d โก m ยท d + n ยท d
ยท-distrib-+สณ zero = sym (identityหก _)
ยท-distrib-+สณ {n} {d} (suc m) =
  begin
    (suc m โข n) ยท d
  โกโจโฉ
    d + (m โข n) ยท d
  โกโจ cong (d +_) (ยท-distrib-+สณ m) โฉ
    (d + (m ยท d + n ยท d))
  โกโจ sym (assoc _ _ _) โฉ
    ((d + m ยท d) + n ยท d)
  โกโจโฉ
    (suc m ยท d + n ยท d)
  โ where open โก-Reasoning

map : (a โ b) โ โ ฯ โ Trie a ฯ โ Trie b ฯ
map f `โฅ = !
map f `โค = f
map f (ฯ `โ ฯ) = map f ฯ โ map f ฯ

map-id : โ ฯ {u : Trie a ฯ} โ map id ฯ u โก u
map-id `โฅ = refl
map-id `โค = refl
map-id (ฯ `โ ฯ) = congโ _,_ (map-id ฯ) (map-id ฯ)

map-โ : โ ฯ {f : a โ b} {g : b โ c} {u : Trie a ฯ} โ map (g โ f) ฯ u โก map g ฯ (map f ฯ u)
map-โ `โฅ = refl
map-โ `โค = refl
map-โ (ฯ `โ ฯ) = congโ _,_ (map-โ ฯ) (map-โ ฯ)

map-cong : โ {f g : a โ b} โ f โ g โ โ ฯ {u : Trie a ฯ} โ map f ฯ u โก map g ฯ u
map-cong fโg `โฅ = refl
map-cong fโg `โค = fโg _
map-cong fโg (ฯ `โ ฯ) = congโ _,_ (map-cong fโg ฯ) (map-cong fโg ฯ)

-- Corollaries

-- TODO: Drop "+" from these names

map-identityหก : โ ฯ {u : Trie ๐ ฯ} โ map (ฮต +_) ฯ u โก u
map-identityหก ฯ = map-cong identityหก ฯ อพ map-id ฯ

map-identityสณ : โ ฯ {u : Trie ๐ ฯ} โ map (_+ ฮต) ฯ u โก u
map-identityสณ ฯ = map-cong identityสณ ฯ อพ map-id ฯ

map-1ยท : โ ฯ {u : Trie ๐ ฯ} โ map (1 ยท d +_) ฯ u โก map (d +_) ฯ u
map-1ยท {d} = map-cong (ฮป x โ cong (_+ x) (identityสณ d))

map-assoc : โ ฯ {u : Trie ๐ ฯ} โ
  map ((d + e) +_) ฯ u โก map (d +_) ฯ (map (e +_) ฯ u)
map-assoc {d = d} {e} ฯ = map-cong (assoc d e) ฯ อพ map-โ ฯ

map-comm : โ ฯ {u : Trie ๐ ฯ} โ map ((d + e) +_) ฯ u โก map ((e + d) +_) ฯ u
map-comm {d = d} {e} = map-cong (ฮป x โ cong (_+ x) (comm d e))

map-+โ+-comm : โ ฯ {u : Trie ๐ ฯ} โ
  map (d +_) ฯ (map (e +_) ฯ u) โก map (e +_) ฯ (map (d +_) ฯ u)
map-+โ+-comm {d = d} {e = e} ฯ =
  sym (map-assoc ฯ) อพ map-comm {e = e} ฯ อพ map-assoc ฯ

map-distribสณ : โ ฯ {u : Trie ๐ ฯ} โ โ m โ
  map ((m โข n) ยท d +_) ฯ u โก map (m ยท d + n ยท d +_) ฯ u
map-distribสณ ฯ m = map-cong (ฮป x โ cong (_+ x) (ยท-distrib-+สณ m)) ฯ

map-distribสณ-assoc : โ ฯ {u : Trie ๐ ฯ} โ โ m โ
  map ((m โข n) ยท d +_) ฯ u โก map (m ยท d +_) ฯ (map (n ยท d +_) ฯ u)
map-distribสณ-assoc ฯ m = map-distribสณ ฯ m อพ map-assoc ฯ

zip : โ ฯ โ Trie a ฯ ร Trie b ฯ โ Trie (a ร b) ฯ
zip `โฅ = unitorแตสณ
zip `โค = id
zip (ฯ `โ ฯ) = (zip ฯ โ zip ฯ) โ transpose

zipโปยน : โ ฯ โ Trie (a ร b) ฯ โ Trie a ฯ ร Trie b ฯ
zipโปยน `โฅ = unitorโฑสณ
zipโปยน `โค = id
zipโปยน (ฯ `โ ฯ) = transpose โ (zipโปยน ฯ โ zipโปยน ฯ)


-- Objects are time tries
record Obj : Set where
  constructor obj
  field
    shape : Shape
    times : Trie ๐ shape
open Obj public

private variable A B C D S : Obj

module timed-obj-instances where instance

  products : Products Obj
  products = record
    { โค = obj `โฅ tt
    ; _ร_ = ฮป (obj ฯ u) (obj ฯ v) โ obj (ฯ `โ ฯ) (u , v)
    }

  boolean : Boolean Obj
  boolean = record { Bool = obj `โค ฮต }

Relocate : (h : ๐ โ ๐) โ Obj โ Obj
Relocate h (obj ฯ ts) = obj ฯ (map h ฯ ts)

Move : ๐ โ Obj โ Obj
Move d = Relocate (d +_)

infixl 7 _ยทฬ_
_ยทฬ_ : Shape โ ๐ โ ๐
ฯ ยทฬ d = size ฯ ยท d

-- Progressively moveed rightward traversal
Moves : ๐ โ Obj โ Shape โ Obj
Moves d A `โฅ = โค
Moves d A `โค = A
Moves d A (ฯ `โ ฯ) = Moves d A ฯ ร Move (ฯ ยทฬ d) (Moves d A ฯ)

-- Morphisms are functions on bit tries
infix 0 _โจ_
record _โจ_ (A B : Obj) : Set where
  constructor mk
  field
    f : Trie ๐น (shape A) โ Trie ๐น (shape B)

module timed-cat-instances where instance

  category : Category _โจ_
  category = record { id = mk id ; _โ_ = ฮป (mk g) (mk f) โ mk (g โ f) }

  cartesian : Cartesian _โจ_
  cartesian = record
    {  !  = mk !
    ; _โต_ = ฮป (mk f) (mk g) โ mk (f โต g)
    ; exl = mk exl
    ; exr = mk exr
    }

  logic : Logic _โจ_
  logic = record
    { false = mk false
    ; true  = mk true
    ; not   = mk not
    ; โง     = mk โง 
    ; โจ     = mk โจ
    ; xor   = mk โ
    ; cond  = mk cond
    }

-- TODO: Define via Subcategory

relocate : โ {g h} โ (A โจ B) โ (Relocate g A โจ Relocate h B)
relocate (mk f) = mk f

move : (A โจ B) โ (Move d A โจ Move d B)
move = relocate
-- move (mk f) = mk f

-- Note: Move d and move form a cartesian (endo)functor.

shift : A โจ Move d A
shift = mk id

-- Apply timing identities
subT : โ {u v : Trie ๐ ฯ} โ v โก u โ obj ฯ u โจ obj ฯ v
subT refl = id
-- subT vโกu = sub id (cong obj (sym vโกu))

-- Temporal version. First version.
mapTโ : โ (f : A โจ B) ฯ โ Moves d A ฯ โจ Moves d B ฯ
mapTโ f `โฅ = !
mapTโ f `โค = f
mapTโ f (ฯ `โ ฯ) = mapTโ f ฯ โ move (mapTโ f ฯ)

-- Generalize mapT to mealyT by adding a running accumulator ("state"):

-- Untimed
mealyโฒ : โ {s} (h : s ร a โ b ร s) ฯ โ s ร Trie a ฯ โ Trie b ฯ ร s
mealyโฒ h `โฅ (x , tt) = tt , x
mealyโฒ h `โค (s , x) = h (s , x)
mealyโฒ h (ฯ `โ ฯ) (s , (xsโ , xsโ)) =
  let ysโ , tโ = mealyโฒ h ฯ (s  , xsโ)
      ysโ , tโ = mealyโฒ h ฯ (tโ , xsโ)
  in (ysโ , ysโ) , tโ

-- Categorical formulation
mealyโณ : โ {s} (h : s ร a โ b ร s) ฯ โ s ร Trie a ฯ โ Trie b ฯ ร s
mealyโณ h `โฅ = unitorโฑหก โ unitorแตสณ -- swap
mealyโณ h `โค = h
mealyโณ h (ฯ `โ ฯ) = assocหก โ second (mealyโณ h ฯ) โ inAssocหก (mealyโณ h ฯ)

-- Categorical formulation
mealy : โ (h : S ร A โจ B ร Move d S) ฯ โ
  S ร Moves d A ฯ โจ Moves d B ฯ ร Move (ฯ ยทฬ d) S
mealy {S} h `โฅ = unitorโฑหก โ subT (map-identityหก (shape S)) โ unitorแตสณ
mealy {S} h `โค = second (subT (map-1ยท (shape S))) โ h
mealy {S} h (ฯ `โ ฯ) =
  assocหก โ
  second (second (subT (map-distribสณ-assoc (shape S) (size ฯ))) โ
          move (mealy h ฯ)) โ
  inAssocหก (mealy h ฯ)

-- The shape of morphism coming out of mealy matches the morphism shape coming
-- in, and thus mealy can be applied repeatedly, e.g., mealy (mealy (mealy h)).
-- More usefully, invert roles of input and state: mealy (swap โ mealy โ swap).
-- See below.

-- TODO: Generalize mealy to nonuniform timing (via prefix sums of timing).

-- mapM as mealyS with empty state (S = โค)
mapM : โ (f : A โจ B) ฯ โ Moves d A ฯ โจ Moves d B ฯ
mapM f ฯ = unitorแตสณ โ mealy (unitorโฑสณ โ f โ unitorแตหก) ฯ โ unitorโฑหก

scan : โ (f : B ร A โจ Move d B) ฯ โ
  B ร Moves d A ฯ โจ Moves d (Move d B) ฯ ร Move (ฯ ยทฬ d) B
scan f = mealy (dup โ f)

fold : โ (f : B ร A โจ Move d B) ฯ โ B ร Moves d A ฯ โจ Move (ฯ ยทฬ d) B
fold f ฯ = exr โ scan f ฯ

-- TODO: Consistent naming scheme. Maybe mapD, scanD, foldD. Later, however,
-- we'll want ยทnonsequentialยท timed variants.

-- Moves-Move : โ n โ Moves d (Move e A) n โก Move e (Moves d A n)
Moves-Move : โ ฯ โ Moves d (Move e A) ฯ โก Move e (Moves d A ฯ)
Moves-Move `โฅ = refl
Moves-Move `โค = refl
Moves-Move {d} {e} {A} (ฯ `โ ฯ) =
  begin
    Moves d (Move e A) (ฯ `โ ฯ)
  โกโจโฉ
    (Moves d (Move e A) ฯ ร Move (ฯ ยทฬ d) (Moves d (Move e A) ฯ))
  โกโจ congโ (ฮป โ โ โ โ ร Move (ฯ ยทฬ d) โ)
           (Moves-Move ฯ) (Moves-Move ฯ) โฉ
    (Move e (Moves d A ฯ) ร Move (ฯ ยทฬ d) (Move e (Moves d A ฯ)))
  โกโจ cong (Move e (Moves d A ฯ) ร_) (cong (obj ฯยท) (map-+โ+-comm ฯยท)) โฉ
    (Move e (Moves d A ฯ) ร Move e (Move (ฯ ยทฬ d) (Moves d A ฯ)))
  โกโจโฉ
    Move e (Moves d A ฯ ร Move (ฯ ยทฬ d) (Moves d A ฯ))
  โกโจโฉ
    Move e (Moves d A (ฯ `โ ฯ))
  โ
 where ฯยท = shape (Moves d A ฯ)
       open โก-Reasoning

zipM : โ ฯ โ Moves d A ฯ ร Moves d B ฯ โจ Moves d (A ร B) ฯ
zipM `โฅ = unitorแตหก
zipM `โค = id
zipM (ฯ `โ ฯ) = (zipM ฯ โ move (zipM ฯ)) โ transpose

zipMโปยน : โ ฯ โ Moves d (A ร B) ฯ โจ Moves d A ฯ ร Moves d B ฯ
zipMโปยน `โฅ = unitorโฑหก
zipMโปยน `โค = id
zipMโปยน (ฯ `โ ฯ) = transpose โ (zipMโปยน ฯ โ move (zipMโปยน ฯ))

-- Note that zipM & zipMโปยน form an isomorphism


---- Experiments in nested (higher-dimensional?) mealy machines

-- Here's where we use commutativity of +:
mealyยฒโ : โ (h : S ร A โจ B ร Move d S) ฯ ฯ โ
  S ร Moves (ฯ ยทฬ d) (Moves d A ฯ) ฯ โจ
    Moves (ฯ ยทฬ d) (Moves d B ฯ) ฯ ร Move (ฯ ยทฬ (ฯ ยทฬ d)) S
mealyยฒโ h ฯ ฯ = mealy (mealy h ฯ) ฯ

private module Foo (h : S ร A โจ Move e A ร Move d S) ฯ where

  fooโ : S ร Moves d A ฯ โจ Moves d (Move e A) ฯ ร Move (ฯ ยทฬ d) S
  fooโ = mealy h ฯ

  fooโ : Moves d A ฯ ร S โจ Move (ฯ ยทฬ d) S ร Moves d (Move e A) ฯ
  fooโ = swap โ mealy h ฯ โ swap

  fooโ : Moves d A ฯ ร S โจ Move (ฯ ยทฬ d) S ร Move e (Moves d A ฯ)
  fooโ = second (subโก (Moves-Move ฯ)) โ swap โ mealy h ฯ โ swap

  fooโ : โ ฯ โ Moves d A ฯ ร Moves e S ฯ โจ
           Moves e (Move (ฯ ยทฬ d) S) ฯ ร Move (ฯ ยทฬ e) (Moves d A ฯ)
  fooโ ฯ = mealy fooโ ฯ

  fooโ : โ ฯ โ Moves d A ฯ ร Moves e S ฯ โจ
           Move (ฯ ยทฬ d) (Moves e S ฯ) ร Move (ฯ ยทฬ e) (Moves d A ฯ)
  fooโ ฯ = first (subโก (Moves-Move ฯ)) โ fooโ ฯ

mealyยฒโ : (h : S ร A โจ Move e A ร Move d S) โ โ ฯ ฯ โ
  Moves d A ฯ ร Moves e S ฯ โจ
     Move (ฯ ยทฬ d) (Moves e S ฯ) ร Move (ฯ ยทฬ e) (Moves d A ฯ)
mealyยฒโ h ฯ ฯ = first (subโก (Moves-Move ฯ)) โ
            mealy (second (subโก (Moves-Move ฯ)) โ swap โ mealy h ฯ โ swap) ฯ


-- Parametrize over spacetime offset for โ and โง gates
module Examples (ฮณ : ๐) where

  โฮณ โงฮณ : ๐น ร ๐น โจ Move ฮณ ๐น
  โฮณ = move โ โ shift
  โงฮณ = move โง โ shift

  -- โฮณ = shift โ โ
  -- โงฮณ = shift โ โง

  -- Half adder with carry-out on right.
  upโ : ๐น ร ๐น โจ Move ฮณ (๐น ร ๐น)
  upโ = โฮณ โต โงฮณ

  -- Conditionally increment an n-bit natural number
  up : โ ฯ โ ๐น ร Moves ฮณ ๐น ฯ โจ Moves ฮณ (Move ฮณ ๐น) ฯ ร Move (ฯ ยทฬ ฮณ) ๐น
  up = mealy upโ

  upยฒ : โ ฯ ฯ โ
    ๐น ร Moves (ฯ ยทฬ ฮณ) (Moves ฮณ ๐น ฯ) ฯ โจ
      Moves (ฯ ยทฬ ฮณ) (Moves ฮณ (Move ฮณ ๐น) ฯ) ฯ ร Move (ฯ ยทฬ (ฯ ยทฬ ฮณ)) ๐น
  upยฒ = mealyยฒโ upโ

  counter : โ ฯ ฯ โ
    Moves ฮณ ๐น ฯ ร Moves ฮณ ๐น ฯ โจ
      Move (ฯ ยทฬ ฮณ) (Moves ฮณ ๐น ฯ) ร Move (ฯ ยทฬ ฮณ) (Moves ฮณ ๐น ฯ)
  counter = mealyยฒโ upโ

  -- counter takes a ฯ-bit initial count and ฯ carries-in and yields ฯ
  -- carries-out and a final ฯ-bit count. Note the lovely symmetry in the type.

-- TODO: Write up notes, including untimed versions of mealyยฒโ and mealyยฒโ (and
-- choose better names).
