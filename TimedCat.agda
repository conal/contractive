-- A category of timed computation. Objects are time tries, and morphisms are
-- computable functions between bit tries (easily generalized to arbitrary
-- atomic types). The relationship to regular computable functions is a simple
-- functor that forgets times. Later, we'll swap out functions (denotation) for
-- a compilable representation, again with a functor back to semantics. As
-- always, implementation correctness is semantic homomorphicity/functoriality.

-- TODO: consider coproducts. What are timing structures for sums? Normally I
-- don't think of sum types as tries, but they're probably *dependent* tries.

module TimedCat where

open import Level using (Level; 0â)
open import Data.Empty.Polymorphic
open import Data.Sum using (_â_)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality as âĄ

open import Categorical.Raw renaming (xor to â; Bool to đš)
open import Functions 0â

private variable
  â o : Level
  a b c : Set

infixr 1 _Íž_   -- unicode
_Íž_ : â {a : Set â} {x y z : a} â x âĄ y â y âĄ z â x âĄ z
_Íž_ = trans

infixr 6 _`â_
data Shape : Set where
  `âĽ : Shape
  `â¤ : Shape
  _`â_  : (Ď Ď : Shape) â Shape

private variable Ď Ď : Shape

size : Shape â â
size `âĽ = 0
size `â¤ = 1
size (Ď `â Ď) = size Ď + size Ď

âŚ_â§ : Shape â Set
âŚ `âĽ â§ = âĽ
âŚ `â¤ â§ = â¤
âŚ Ď `â Ď â§ = âŚ Ď â§ â âŚ Ď â§

đ˝ : â â Shape
đ˝ zero = `âĽ
đ˝ (suc n) = `â¤ `â đ˝ n

Trie : {obj : Set o} âŚ _ : Products obj âŚ â obj â Shape â obj
Trie a `âĽ = â¤
Trie a `â¤ = a
Trie a (Ď `â Ď) = Trie a Ď Ă Trie a Ď

-- Trie a Ď â âŚ Ď â§ â a

private variable u v : Trie a Ď

-- "Time", which could be â, â, or an arbitrary commutative monoid such as
-- spacetime.
đ : Set
đ = â

private variable m n : â ; s t d e : đ

map : (a â b) â â Ď â Trie a Ď â Trie b Ď
map f `âĽ = !
map f `â¤ = f
map f (Ď `â Ď) = map f Ď â map f Ď

map-id : â Ď {u : Trie a Ď} â map id Ď u âĄ u
map-id `âĽ = refl
map-id `â¤ = refl
map-id (Ď `â Ď) = congâ _,_ (map-id Ď) (map-id Ď)

map-â : â Ď {f : a â b} {g : b â c} {u : Trie a Ď} â map (g â f) Ď u âĄ map g Ď (map f Ď u)
map-â `âĽ = refl
map-â `â¤ = refl
map-â (Ď `â Ď) = congâ _,_ (map-â Ď) (map-â Ď)

map-cong : â {f g : a â b} â f â g â â Ď {u : Trie a Ď} â map f Ď u âĄ map g Ď u
map-cong fâg `âĽ = refl
map-cong fâg `â¤ = fâg _
map-cong fâg (Ď `â Ď) = congâ _,_ (map-cong fâg Ď) (map-cong fâg Ď)

-- Corollaries

map-+-identityËĄ : â Ď {u : Trie đ Ď} â map (0 +_) Ď u âĄ u
map-+-identityËĄ = map-id

map-+-identityĘł : â Ď {u : Trie đ Ď} â map (_+ 0) Ď u âĄ u
map-+-identityĘł Ď = map-cong +-identityĘł Ď Íž map-id Ď

map-+-1* : â Ď {u : Trie đ Ď} â map (1 * d +_) Ď u âĄ map (d +_) Ď u
map-+-1* {d} = map-cong (Îť x â cong (_+ x) (+-identityĘł d))

map-+-assoc : â Ď {u : Trie đ Ď} â
  map ((d + e) +_) Ď u âĄ map (d +_) Ď (map (e +_) Ď u)
map-+-assoc {d = d} {e} Ď = map-cong (+-assoc d e) Ď Íž map-â Ď

map-+-comm : â Ď {u : Trie đ Ď} â map ((d + e) +_) Ď u âĄ map ((e + d) +_) Ď u
map-+-comm {d = d} {e} = map-cong (Îť x â cong (_+ x) (+-comm d e))

map-+â+-comm : â Ď {u : Trie đ Ď} â
  map (d +_) Ď (map (e +_) Ď u) âĄ map (e +_) Ď (map (d +_) Ď u)
map-+â+-comm {d = d} {e = e} Ď =
  sym (map-+-assoc Ď) Íž map-+-comm {e = e} Ď Íž map-+-assoc Ď

map-+-distribĘł : â Ď {u : Trie đ Ď} â â m â
  map ((m + n) * d +_) Ď u âĄ map (m * d + n * d +_) Ď u
map-+-distribĘł Ď m = map-cong (Îť x â cong (_+ x) (*-distribĘł-+ _ m _)) Ď

map-+-distribĘł-assoc : â Ď {u : Trie đ Ď} â â m â
  map ((m + n) * d +_) Ď u âĄ map (m * d +_) Ď (map (n * d +_) Ď u)
map-+-distribĘł-assoc Ď m = map-+-distribĘł Ď m Íž map-+-assoc Ď

zip : â Ď â Trie a Ď Ă Trie b Ď â Trie (a Ă b) Ď
zip `âĽ = unitoráľĘł
zip `â¤ = id
zip (Ď `â Ď) = (zip Ď â zip Ď) â transpose

zipâťÂš : â Ď â Trie (a Ă b) Ď â Trie a Ď Ă Trie b Ď
zipâťÂš `âĽ = unitorâąĘł
zipâťÂš `â¤ = id
zipâťÂš (Ď `â Ď) = transpose â (zipâťÂš Ď â zipâťÂš Ď)


-- Objects are time tries
record Obj : Set where
  constructor obj
  field
    shape : Shape
    times : Trie đ shape
open Obj public

private variable A B C D S : Obj

module timed-obj-instances where instance

  products : Products Obj
  products = record
    { â¤ = obj `âĽ tt
    ; _Ă_ = Îť (obj Ď u) (obj Ď v) â obj (Ď `â Ď) (u , v)
    }

  boolean : Boolean Obj
  boolean = record { Bool = obj `â¤ 0 }

Retime : (h : đ â đ) â Obj â Obj
Retime h (obj Ď ts) = obj Ď (map h Ď ts)

Delay : đ â Obj â Obj
Delay d = Retime (d +_)

infixl 7 _*Ě_
_*Ě_ : Shape â đ â đ
Ď *Ě d = size Ď * d

-- Progressively delayed rightward traversal
Delays : đ â Obj â Shape â Obj
Delays d A `âĽ = â¤
Delays d A `â¤ = A
Delays d A (Ď `â Ď) = Delays d A Ď Ă Delay (Ď *Ě d) (Delays d A Ď)

-- Morphisms are functions on bit tries
infix 0 _â¨_
record _â¨_ (A B : Obj) : Set where
  constructor mk
  field
    f : Trie đš (shape A) â Trie đš (shape B)

module timed-cat-instances where instance

  category : Category _â¨_
  category = record { id = mk id ; _â_ = Îť (mk g) (mk f) â mk (g â f) }

  cartesian : Cartesian _â¨_
  cartesian = record
    {  !  = mk !
    ; _âľ_ = Îť (mk f) (mk g) â mk (f âľ g)
    ; exl = mk exl
    ; exr = mk exr
    }

  logic : Logic _â¨_
  logic = record
    { false = mk false
    ; true  = mk true
    ; not   = mk not
    ; â§     = mk â§ 
    ; â¨     = mk â¨
    ; xor   = mk â
    ; cond  = mk cond
    }

-- TODO: Define via Subcategory

retime : â {g h} â (A â¨ B) â (Retime g A â¨ Retime h B)
retime (mk f) = mk f

delay : (A â¨ B) â (Delay d A â¨ Delay d B)
delay = retime
-- delay (mk f) = mk f

-- Note: Delay d and delay form a cartesian (endo)functor.

pause : A â¨ Delay d A
pause = mk id

-- Apply timing identities
subT : â {u v : Trie đ Ď} â v âĄ u â obj Ď u â¨ obj Ď v
subT refl = id
-- subT vâĄu = sub id (cong obj (sym vâĄu))

-- Temporal version. First version.
mapTâ : â (f : A â¨ B) Ď â Delays d A Ď â¨ Delays d B Ď
mapTâ f `âĽ = !
mapTâ f `â¤ = f
mapTâ f (Ď `â Ď) = mapTâ f Ď â delay (mapTâ f Ď)

-- Generalize mapT to mealyT by adding a running accumulator ("state"):

-- Untimed
mealyâ˛ : â {s} (h : s Ă a â b Ă s) Ď â s Ă Trie a Ď â Trie b Ď Ă s
mealyâ˛ h `âĽ (x , tt) = tt , x
mealyâ˛ h `â¤ (s , x) = h (s , x)
mealyâ˛ h (Ď `â Ď) (s , (xsâ , xsâ)) =
  let ysâ , tâ = mealyâ˛ h Ď (s  , xsâ)
      ysâ , tâ = mealyâ˛ h Ď (tâ , xsâ)
  in (ysâ , ysâ) , tâ

-- Categorical formulation
mealyâł : â {s} (h : s Ă a â b Ă s) Ď â s Ă Trie a Ď â Trie b Ď Ă s
mealyâł h `âĽ = unitorâąËĄ â unitoráľĘł -- swap
mealyâł h `â¤ = h
mealyâł h (Ď `â Ď) = assocËĄ â second (mealyâł h Ď) â inAssocËĄ (mealyâł h Ď)

-- Categorical formulation
mealy : â (h : S Ă A â¨ B Ă Delay d S) Ď â
  S Ă Delays d A Ď â¨ Delays d B Ď Ă Delay (Ď *Ě d) S
mealy {S} h `âĽ = unitorâąËĄ â subT (map-+-identityËĄ (shape S)) â unitoráľĘł
mealy {S} h `â¤ = second (subT (map-+-1* (shape S))) â h
mealy {S} h (Ď `â Ď) =
  assocËĄ â
  second (second (subT (map-+-distribĘł-assoc (shape S) (size Ď))) â
          delay (mealy h Ď)) â
  inAssocËĄ (mealy h Ď)

-- The shape of morphism coming out of mealy matches the morphism shape coming
-- in, and thus mealy can be applied repeatedly, e.g., mealy (mealy (mealy h)).
-- More usefully, invert roles of input and state: mealy (swap â mealy â swap).
-- See below.

-- TODO: Generalize mealy to nonuniform timing (via prefix sums of timing).

-- mapT as mealyS with empty state (S = â¤)
mapT : â (f : A â¨ B) Ď â Delays d A Ď â¨ Delays d B Ď
mapT f Ď = unitoráľĘł â mealy (unitorâąĘł â f â unitoráľËĄ) Ď â unitorâąËĄ

scan : â (f : B Ă A â¨ Delay d B) Ď â
  B Ă Delays d A Ď â¨ Delays d (Delay d B) Ď Ă Delay (Ď *Ě d) B
scan f = mealy (dup â f)

fold : â (f : B Ă A â¨ Delay d B) Ď â B Ă Delays d A Ď â¨ Delay (Ď *Ě d) B
fold f Ď = exr â scan f Ď

-- TODO: Consistent naming scheme. Maybe mapD, scanD, foldD. Later, however,
-- we'll want *nonsequential* timed variants.

---- Examples


-- Gate delay
Îł : đ
Îł = 2

âÎł â§Îł : đš Ă đš â¨ Delay Îł đš
âÎł = delay â â pause
â§Îł = delay â§ â pause

-- âÎł = pause â â
-- â§Îł = pause â â§

-- Half adder with carry-out on right.
upâ : đš Ă đš â¨ Delay Îł (đš Ă đš)
upâ = âÎł âľ â§Îł

-- Conditionally increment an n-bit natural number
up : â Ď â đš Ă Delays Îł đš Ď â¨ Delays Îł (Delay Îł đš) Ď Ă Delay (Ď *Ě Îł) đš
up = mealy upâ

-- Delays-Delay : â n â Delays d (Delay e A) n âĄ Delay e (Delays d A n)
Delays-Delay : â Ď â Delays d (Delay e A) Ď âĄ Delay e (Delays d A Ď)
Delays-Delay `âĽ = refl
Delays-Delay `â¤ = refl
Delays-Delay {d} {e} {A} (Ď `â Ď) =
  begin
    Delays d (Delay e A) (Ď `â Ď)
  âĄâ¨âŠ
    (Delays d (Delay e A) Ď Ă Delay (Ď *Ě d) (Delays d (Delay e A) Ď))
  âĄâ¨ congâ (Îť â â â â Ă Delay (Ď *Ě d) â)
           (Delays-Delay Ď) (Delays-Delay Ď) âŠ
    (Delay e (Delays d A Ď) Ă Delay (Ď *Ě d) (Delay e (Delays d A Ď)))
  âĄâ¨ cong (Delay e (Delays d A Ď) Ă_) (cong (obj Ď*) (map-+â+-comm Ď*)) âŠ
    (Delay e (Delays d A Ď) Ă Delay e (Delay (Ď *Ě d) (Delays d A Ď)))
  âĄâ¨âŠ
    Delay e (Delays d A Ď Ă Delay (Ď *Ě d) (Delays d A Ď))
  âĄâ¨âŠ
    Delay e (Delays d A (Ď `â Ď))
  â
 where Ď* = shape (Delays d A Ď)
       open âĄ-Reasoning

zipD : â Ď â Delays d A Ď Ă Delays d B Ď â¨ Delays d (A Ă B) Ď
zipD `âĽ = unitoráľËĄ
zipD `â¤ = id
zipD (Ď `â Ď) = (zipD Ď â delay (zipD Ď)) â transpose

zipDâťÂš : â Ď â Delays d (A Ă B) Ď â¨ Delays d A Ď Ă Delays d B Ď
zipDâťÂš `âĽ = unitorâąËĄ
zipDâťÂš `â¤ = id
zipDâťÂš (Ď `â Ď) = transpose â (zipDâťÂš Ď â delay (zipDâťÂš Ď))

-- Note that zipD & zipDâťÂš form an isomorphism


---- Experiments in nested (higher-dimensional?) mealy machines

mealyÂ˛â : â (h : S Ă A â¨ B Ă Delay d S) Ď Ď â
  S Ă Delays (Ď *Ě d) (Delays d A Ď) Ď â¨
    Delays (Ď *Ě d) (Delays d B Ď) Ď Ă Delay (Ď *Ě (Ď *Ě d)) S
mealyÂ˛â h Ď Ď = mealy (mealy h Ď) Ď

upÂ˛ : â Ď Ď â
  đš Ă Delays (Ď *Ě Îł) (Delays Îł đš Ď) Ď â¨
    Delays (Ď *Ě Îł) (Delays Îł (Delay Îł đš) Ď) Ď Ă Delay (Ď *Ě (Ď *Ě Îł)) đš
upÂ˛ = mealyÂ˛â upâ

private module Foo (h : S Ă A â¨ Delay e A Ă Delay d S) Ď where

  fooâ : S Ă Delays d A Ď â¨ Delays d (Delay e A) Ď Ă Delay (Ď *Ě d) S
  fooâ = mealy h Ď

  fooâ : Delays d A Ď Ă S â¨ Delay (Ď *Ě d) S Ă Delays d (Delay e A) Ď
  fooâ = swap â mealy h Ď â swap

  fooâ : Delays d A Ď Ă S â¨ Delay (Ď *Ě d) S Ă Delay e (Delays d A Ď)
  fooâ = second (subâĄ (Delays-Delay Ď)) â swap â mealy h Ď â swap

  fooâ : â Ď â Delays d A Ď Ă Delays e S Ď â¨
           Delays e (Delay (Ď *Ě d) S) Ď Ă Delay (Ď *Ě e) (Delays d A Ď)
  fooâ Ď = mealy fooâ Ď

  fooâ : â Ď â Delays d A Ď Ă Delays e S Ď â¨
           Delay (Ď *Ě d) (Delays e S Ď) Ă Delay (Ď *Ě e) (Delays d A Ď)
  fooâ Ď = first (subâĄ (Delays-Delay Ď)) â fooâ Ď

mealyÂ˛â : (h : S Ă A â¨ Delay e A Ă Delay d S) â â Ď Ď â
  Delays d A Ď Ă Delays e S Ď â¨
     Delay (Ď *Ě d) (Delays e S Ď) Ă Delay (Ď *Ě e) (Delays d A Ď)
mealyÂ˛â h Ď Ď = first (subâĄ (Delays-Delay Ď)) â
            mealy (second (subâĄ (Delays-Delay Ď)) â swap â mealy h Ď â swap) Ď

counter : â Ď Ď â
  Delays Îł đš Ď Ă Delays Îł đš Ď â¨
    Delay (Ď *Ě Îł) (Delays Îł đš Ď) Ă Delay (Ď *Ě Îł) (Delays Îł đš Ď)
counter = mealyÂ˛â upâ

-- counter takes a Ď-bit initial count and Ď carries-in and yields Ď
-- carries-out and a final Ď-bit count. Note the lovely symmetry in the type.

-- TODO: Write up notes, including untimed versions of mealyÂ˛â and mealyÂ˛â (and
-- choose better names).
