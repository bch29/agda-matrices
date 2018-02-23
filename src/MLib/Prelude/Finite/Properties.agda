module MLib.Prelude.Finite.Properties where

open import MLib.Prelude.FromStdlib
open import MLib.Prelude.Finite
import MLib.Prelude.Fin as Fin
import MLib.Prelude.Fin.Pieces as P
open Fin using (Fin)

open import Data.List.All as All using (All; []; _∷_) hiding (module All)

open import Function.LeftInverse using (LeftInverse; _↞_) renaming (_∘_ to _ⁱ∘_)
open import Function.Inverse using (Inverse; _↔_)
open import Function.Equality as FE using (_⟶_; _⟨$⟩_; cong)
open import Function.Related using () renaming (module EquationalReasoning to RelReasoning)

open Algebra using (IdempotentCommutativeMonoid)

open Table
open List using ([]; _∷_)

module _ {c ℓ} (finiteSet : FiniteSet c ℓ) where
  open FiniteSet finiteSet renaming (Carrier to A)

  private
    enumTableAt : ∀ {N} → OntoFin N → Table A N
    enumTableAt ontoFin = tabulate (LeftInverse.from ontoFin ⟨$⟩_)

  module _ {c ℓ} (icMonoid : IdempotentCommutativeMonoid c ℓ) where
    module S = IdempotentCommutativeMonoid icMonoid
    open S using (_∙_; ∙-cong) renaming (Carrier to S; _≈_ to _≈′_)
    open import Algebra.Operations.CommutativeMonoid S.commutativeMonoid
    open import Algebra.Properties.CommutativeMonoid S.commutativeMonoid

    private
      module _ {n : ℕ} (ontoFin′ : OntoFin (Nat.suc n)) where
        from = LeftInverse.from ontoFin′ ⟨$⟩_
        to = LeftInverse.to ontoFin′ ⟨$⟩_

        enumTable′ : Table A (Nat.suc n)
        enumTable′ = enumTableAt ontoFin′

        ap : setoid ⟶ S.setoid → A → S
        ap = _⟨$⟩_

        enumTable-complete′ : ∀ (func : setoid ⟶ S.setoid) x → (func ⟨$⟩ x) ∙ sumTable (map (ap func) enumTable′) ≈′ sumTable (map (ap func) enumTable′)
        enumTable-complete′ func x =
          begin
            f x ∙ sumTable (map f enumTable′)                                         ≈⟨ ∙-cong S.refl (sumTable-permute (map f enumTable′) (Fin.swapIndices Fin.zero i)) ⟩
            f x ∙ sumTable (permute (Fin.swapIndices Fin.zero i) (map f enumTable′))  ≡⟨⟩
            f x ∙ (f (from (to x)) ∙ _)                                               ≈⟨ ∙-cong S.refl (∙-cong (cong func (LeftInverse.left-inverse-of ontoFin′ x)) S.refl) ⟩
            f x ∙ (f x ∙ _)                                                           ≈⟨ S.sym (S.assoc _ _ _) ⟩
            (f x ∙ f x) ∙ _                                                           ≈⟨ ∙-cong (S.idem _) S.refl ⟩
            f x ∙ _                                                                   ≈⟨ ∙-cong (cong func (sym (LeftInverse.left-inverse-of ontoFin′ x))) S.refl ⟩
            f (from (to x)) ∙ _                                                       ≡⟨⟩
            sumTable (permute (Fin.swapIndices Fin.zero i) (map f enumTable′))        ≈⟨ S.sym (sumTable-permute (map f enumTable′) (Fin.swapIndices Fin.zero i)) ⟩
            sumTable (map f enumTable′)                                               ∎
          where
            f = ap func
            i = to x

            open EqReasoning S.setoid

    private
      inhabited : ∀ {N} (i : Fin N) → ∃ λ n → N ≡ Nat.suc n
      inhabited Fin.zero = _ , ≡.refl
      inhabited (Fin.suc i) = _ , ≡.refl

      enumTable-complete′′ :
        ∀ {N} (ontoFin′ : OntoFin N) (f : setoid ⟶ S.setoid) x
        → (f ⟨$⟩ x) ∙ sumTable (Table.map (f ⟨$⟩_) (enumTableAt ontoFin′))
          ≈′ sumTable (Table.map (f ⟨$⟩_) (enumTableAt ontoFin′))
      enumTable-complete′′ ontoFin′ f x with inhabited (LeftInverse.to ontoFin′ ⟨$⟩ x)
      enumTable-complete′′ ontoFin′ f x | n , ≡.refl = enumTable-complete′ ontoFin′ f x

      sum/map-hom : ∀ {n} {a}{A : Set a} (f : A → S) (t : Table A n) → sum (List.map f (toList t)) ≡ sumTable (map f t)
      sum/map-hom f t =
        begin
          sum (List.map f (toList t))   ≡⟨ ≡.cong sum (Table.map-toList-hom t) ⟩
          sum (toList (map f t))        ≡⟨ ≡.sym (sumTable-toList (map f t)) ⟩
          sumTable (map f t)            ∎
        where
          open ≡.Reasoning


    -- Enumeration is complete: in any idempotent commutative monoid, adding one
    -- more element to the sum won't change it. In particular, this works in the
    -- powerset monoid, where 'f' is the singleton at its argument and addition
    -- is set union. This shows that every member of 'A' is present in the
    -- enumeration (even though the powerset monoid is quite difficult to
    -- implement in Agda so this proof is not present).

    enumTable-complete : ∀ f x → (f ⟨$⟩ x) ∙ sumTable (map (f ⟨$⟩_) enumTable) ≈′ sumTable (map (f ⟨$⟩_) enumTable)
    enumTable-complete = enumTable-complete′′ ontoFin

    enumerate-complete : ∀ (f : setoid ⟶ S.setoid) x → (f ⟨$⟩ x) ∙ sum (List.map (f ⟨$⟩_) enumerate) ≈′ sum (List.map (f ⟨$⟩_) enumerate)
    enumerate-complete func x =
      begin
        f x ∙ sum (List.map f enumerate)           ≡⟨⟩
        f x ∙ sum (List.map f (toList enumTable))  ≡⟨ ≡.cong₂ _∙_ ≡.refl (sum/map-hom f enumTable) ⟩
        f x ∙ sumTable (map f enumTable)           ≈⟨ enumTable-complete func x ⟩
        sumTable (map f enumTable)                 ≡⟨ ≡.sym (sum/map-hom f enumTable) ⟩
        sum (List.map f enumerate)                 ∎
      where
        f = func ⟨$⟩_
        open EqReasoning S.setoid
