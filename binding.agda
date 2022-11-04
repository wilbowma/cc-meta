open import Level using (Level; suc)
open import Data.Nat using (ℕ; _+_; zero; _<_) renaming (suc to add1)
open import Agda.Builtin.Equality using (_≡_) renaming
  (refl to base-refl)
open import Relation.Binary.PropositionalEquality.Core using (cong; icong) renaming
  (sym to base-sym;
   trans to base-trans;
   subst to base-subst)
open import Data.Sum.Base
open import Data.Unit.Base using (⊤; tt)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product



-- A theory of binding/substitution that map variables to values in X
record Theory-of-Binding (X : Set) : Set₁ where
  field
    Var : Set
    -- {{EquivVar}} : Equiv Var
    -- {{EquivX}} : Equiv X
    Scope : Set
  Subst = (Var -> X)
  aTerm = Subst -> X
  field
    extend : (x : X) -> (ρ : Subst) -> Subst × Var
    extend/apply : ∀ {x ρ} -> let (ρ' , v) = (extend x ρ) in (ρ' v) ≡ x
    extend/skip : ∀ {x ρ v'} -> let (ρ' , v) = (extend x ρ) in ¬ (v ≡ v') -> (ρ' v') ≡ (ρ v')
    --(λ ρ' -> Σ Var λ v -> (ρ' v) ≡ x × ((x : Var) -> (ρ' x) ≡ (ρ x)))
    --extend : Subst -> Var -> X -> Subst
    rename : Var -> Scope -> Var
    relocate : Subst -> Scope -> Subst
    freshen : Scope -> X
    bind : Var -> X -> X
    relocate/rename : ∀ {ρ s n} -> relocate ρ s n ≡ ρ (rename n s)
    --extend/apply : ∀ {ρ x v} -> (extend ρ v x) v ≡ x
    --extend/skip : ∀ {ρ x v1 v2} -> ¬ (v1 ≡ v2) -> (extend ρ v1 x) v2 ≡ (ρ v2)
    --subst/α : ∀ {ρ x v1 v2 v} -> (extend ρ v1 x) ≡ (extend ρ v2 x)
    --subst/α' : ∀ {ρ x v1 v2 v} -> ((extend ρ v1 x) v) ≡ ((extend ρ v2 x) v)

module example-de-Bruijn (X : Set) where
  open Theory-of-Binding {{...}}
  instance
    de-Bruijn : Theory-of-Binding X
    Var {{de-Bruijn}} = ℕ
    Scope {{de-Bruijn}} = ℕ
    extend {{de-Bruijn}} x ρ = ((λ {zero -> x;
                                   (add1 y) -> (ρ y)}) , zero)

    extend/apply {{de-Bruijn}} = base-refl
    extend/skip ⦃ de-Bruijn ⦄ {x = x} {ρ = ρ} {v' = zero} P = ⊥-elim (P base-refl)
    extend/skip ⦃ de-Bruijn ⦄ {x = x} {ρ = ρ} {v' = add1 v''} _ = {!!}
