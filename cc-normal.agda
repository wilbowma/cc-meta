open import Level using (Level; suc)
open import Data.Nat using (ℕ; _+_; zero; _<_) renaming (suc to add1)
open import Agda.Builtin.Equality using (_≡_) renaming
  (refl to base-refl)
open import Relation.Binary.PropositionalEquality.Core using () renaming
  (sym to base-sym;
   trans to base-trans)
open import Data.Sum.Base
open import Data.Unit.Base using (⊤)
open import Relation.Nullary using (¬_)

record Equiv {a} (A : Set a) : Set (suc a) where
  field
     _==_ : A -> A -> Set
     refl : (x : A) -> x == x
     sym : (x y : A) -> x == y -> y == x
     trans : (x y z : A) -> x == y -> y == z -> x == z

-- Binds ==, refl, sym, and trans.
open Equiv {{...}}

-- As an example of using records as interfaces, lets instantiate Equiv to an
-- equality relation on booleans.
module example where
  data Bool : Set where
    true : Bool
    false : Bool

  data BoolEq : Bool -> Bool -> Set where
    brefl : (x : Bool) -> BoolEq x x

  bsym : ∀ {x y} -> BoolEq x y -> BoolEq y x
  -- these proof terms weren't written down manually, but using agda-mode to
  -- generate them.
  -- the .x means Agda figured out that y is actually
  bsym {x} {.x} (brefl .x) = brefl x

  btrans : ∀ {x y z} -> BoolEq x y -> BoolEq y z -> BoolEq x z
  btrans {x} {.x} {.x} (brefl .x) (brefl .x) = brefl x

  instance
    EqBool : Equiv Bool
    _==_ {{EqBool}} = BoolEq
    refl {{EqBool}} = brefl
    -- Change of interface: bsym and btrans leave the actual bools implicit, but
    -- our definition requires they not be.
    sym {{EqBool}} = λ x y -> bsym {x} {y}
    trans {{EqBool}} = λ x y z -> btrans {x} {y} {z}

record Abstract_CC_Model : Set₁ where
  field
    X : Set
    _∈_ : X -> X -> Set
    -- Declare that the model contains an instance of an Equiv relation on X.
    -- This gives us access to ==, refl, sym, and trans over X
    {{EquivX}} : Equiv X
    props : X
    app : X -> X -> X
    lam : X -> (X -> X) -> X
    Pi : X -> (X -> X) -> X

    -- Semantic inference rules

    Pi-I : ∀ {x A f F} ->
      (x ∈ A) ->
      ((f x) ∈ (F x)) ->
      ------------------------------
      ((lam A f) ∈ (Pi A F))

    Pi-E : ∀ {M N A B} ->
      (M ∈ (Pi A B)) -> (N ∈ A) ->
      ------------------------------
      (app M N) ∈ (B N)

    Imp : ∀ {A B} ->
      (∀ {x} -> (B x) ∈ props) ->
      ----------
      (Pi A B) ∈ props

    β : ∀ {A F N} ->
      (N ∈ A) ->
      ------------
      (app (lam A F) N) == (F N)

    λ-ext : ∀ {A A' f f'} ->
      (A == A') ->
      (∀ {x} -> (x ∈ A) -> (f x) == (f' x)) ->
      ----------
      (lam A f) == (lam A' f')

    Π-ext : ∀ {A A' B B'} ->
      (A == A') ->
      (∀ {x} -> (x ∈ A) -> (B x) == (B' x)) ->
      ----------
      (Pi A B) == (Pi A' B')

    -- "implicit"? according to the text, but then explicitly define
    app-ext : ∀ {M M' N N'} ->
      M == M' -> N == N' ->
      ----------------------
      (app M N) == (app M' N')

    conv-ext : ∀ {x x' y y'} ->
      x ∈ y -> x == x' -> y == y' ->
      -----------------
      x' ∈ y'

    -- extensionality, not required
    -- ext : ∀ {x y} ->
    --   (∀ {z} -> ((z ∈ x) iff (z ∈ y)))->
    --   -------
    --   x == y

    -- "weak extensionality", eta
    η : ∀ {f A B} ->
      f ∈ (Pi A B) ->
      ----------
      f == (lam A (λ x -> (app f x)))


-- The syntax of CC

-- I'm following a deep embedding approach, I think, whereas Bruno follows a
-- shallow embedding approach here.
-- This means that, for Bruno, the definition of each term is defining Val, but
-- I have to define Val by induction over syntax.
data CC_Term : Set where
  cc-Prop : CC_Term
  var : ℕ -> CC_Term
  cc-app : CC_Term -> CC_Term -> CC_Term
  cc-lam : CC_Term -> CC_Term -> CC_Term
  cc-Pi : CC_Term -> CC_Term -> CC_Term
  -- TODO:
  -- Looks like the syntax, Figure 5.2, includes explicit syntax for subst and
  -- relocation. Need to add those
  relocate : (by : ℕ) -> (term : CC_Term) -> CC_Term
  subst : (by : CC_Term) -> (M : CC_Term) -> CC_Term

-- CC Types also include "Kind".
-- Represent the syntax of types as either a term or Kind.
-- This seems to be used to avoid including Kind in the term syntax, and thus
-- trivially make Val total.
-- ... at the expense of making El complicated.
-- Also, doesn't work for higher universes?
data CC_Kind : Set where
  cc-preKind : CC_Kind

CC_Type : Set
CC_Type = CC_Term ⊎ CC_Kind

cc-Kind : CC_Type
cc-Kind = inj₂ cc-preKind

data Ctx : ℕ -> Set where
  cempty : Ctx 0
  snoc : ∀ {n} -> Ctx n -> CC_Term -> Ctx (add1 n)

lookup : ∀ {n} -> Ctx n -> (m : ℕ) -> m < n -> CC_Term
lookup cempty n ()
lookup (snoc Γ x) zero p = x
lookup (snoc Γ x) (add1 n) (Data.Nat.s≤s p) = (lookup Γ n p)

data _⊢_::_ : ∀ {n} -> Ctx n -> CC_Term -> CC_Type -> Set where
  rule-Prop : ∀ {n} {Γ : Ctx n} -> Γ ⊢ cc-Prop :: cc-Kind
  rule-Var : ∀ {n m p A} {Γ : Ctx m} ->
    (lookup Γ n p) ≡ A ->
    ------------------
    Γ ⊢ (var n) :: (inj₁ (relocate (n + 1) A))

  rule-Lam : ∀ {n A Γ M B} ->
    (snoc {n} Γ A) ⊢ M :: (inj₁ B) ->
    -- implicit
    -- ¬ (B ≡ cc-Kind) ->
    ------------------
    Γ ⊢ (cc-lam A M) :: (inj₁ (cc-Pi A B))

-- Now, we prove stuff about any model
module Construction (model : Abstract_CC_Model) where
  -- Can now freely refer to X, etc, as the parameters of an arbirary model.
  open Abstract_CC_Model (model)
  -- A substitution
  Subst = (ℕ -> X)
  -- Is this right?
  SCons : X -> Subst -> Subst
  SCons X ρ zero = X
  SCons X ρ (add1 n) = ρ n

  -- The value interpretation of CC Syntax into some CC Model
  Val : CC_Term -> Subst -> X
  Val cc-Prop ρ = props
  Val (var x) ρ = ρ x
  Val (cc-app M N) ρ = app (Val M ρ) (Val N ρ)
  Val (cc-lam A M) ρ = lam (Val A ρ) (λ x -> (Val M) (SCons x ρ))
  Val (cc-Pi A B) ρ = Pi (Val A ρ) (λ x -> (Val B) (SCons x ρ))
  Val (relocate n M) ρ = Val M (λ i -> (ρ (i + n)))
  Val (subst by M) ρ = Val M (SCons (Val by ρ) ρ)

  -- compositionality properties of Val
  prop1 : ∀ {n ρ} -> Val (relocate 1 (var n)) ρ ≡ (Val (var (n + 1)) ρ)
  prop1 = base-refl

  prop2 : ∀ {M ρ} -> Val (subst M (var 0)) ρ ≡ (Val M ρ)
  prop2 = base-refl

  prop3 : ∀ {M ρ n} -> Val (subst M (var (add1 n))) ρ ≡ (Val (var n) ρ)
  prop3 = base-refl

  El : (T : CC_Type) -> Subst -> X ⊎ (T ≡ cc-Kind)
  El (inj₂ cc-preKind) ρ = inj₂ base-refl
  El (inj₁ x) ρ = inj₁ (Val x ρ)

  -- A different way of writing El, which might be easier to read and write.
  _∈_EL_ : X -> Subst -> CC_Type -> Set
  x ∈ ρ EL (inj₂ cc-preKind) = ⊤
  x ∈ ρ EL (inj₁ A) = (x ≡ Val A ρ)

  empty : Subst

  example1 : {{SomeModel : Abstract_CC_Model}} -> (Val cc-Prop empty) ∈ empty EL cc-Kind
  example1 = Data.Unit.Base.tt

-------
-- A particular model exists.
-- In Bruno's thesis, he defines set theory, then instantiates X to be set
-- (small set, not Coq's Set).
-- I guess I could do that, if I wanted to formalize set theory?
-- I'd need only some of the axioms, I think...

-- I'm going to construct the initial model: instantiate the abstract model with
-- the syntax.

module initial_cc_model where
  open Abstract_CC_Model {{...}}
  instance
    EquivCC_Type : Equiv CC_Type
    _==_ {{EquivCC_Type}} = _≡_
    refl {{EquivCC_Type}} = λ x -> base-refl {x = x}
    sym {{EquivCC_Type}} = λ x y -> base-sym {x = x} {y = y}
    trans {{EquivCC_Type}} = λ x y z -> base-trans {i = x} {j = y} {k = z}

  instance
    InitialCC : Abstract_CC_Model
    X {{InitialCC}} = CC_Term
    props {{InitialCC}} = cc-Prop
    -- Ahhh; distinction between open term in the syntax and closed terms in the model.
    lam {{InitialCC}} = λ x y -> cc-lam ? ?
