module MLib.Prelude.FiniteInj where

open import MLib.Prelude.FromStdlib
import MLib.Prelude.Fin as Fin
open Fin using (Fin)

module Table where
  open import Data.Table public
  open import Data.Table.Properties public
open Table using (Table; tabulate; lookup) hiding (module Table)

open import Function.LeftInverse using (LeftInverse; _↞_)
open import Function.Equality using (_⟶_; _⟨$⟩_; cong)

open Algebra using (IdempotentCommutativeMonoid)

record Finite {a} (A : Set a) : Set a where
  field
    -- Upper bound on the size of the set
    N : ℕ
    fromFin : A ↞ Fin N

  open Table hiding (setoid)
  open List using ([]; _∷_)

  enumerateTable : Table A N
  enumerateTable = tabulate (LeftInverse.from fromFin ⟨$⟩_)

  enumerate : List A
  enumerate = Table.toList enumerateTable

  module _ {c ℓ} (icMonoid : IdempotentCommutativeMonoid c ℓ) where
    open IdempotentCommutativeMonoid icMonoid renaming (Carrier to S)
    open import Algebra.Operations.CommutativeMonoid commutativeMonoid
    open import Algebra.Properties.CommutativeMonoid commutativeMonoid

    private
      module _ {n : ℕ} (fromFin′ : A ↞ Fin (Nat.suc n)) where
        from = LeftInverse.from fromFin′ ⟨$⟩_
        to = LeftInverse.to fromFin′ ⟨$⟩_

        enumTable′ : Table A (Nat.suc n)
        enumTable′ = tabulate from

        enumerate′ : List A
        enumerate′ = Table.toList enumTable′

        enumTable-complete′ : ∀ (f : ≡.setoid A ⟶ setoid) x → (f ⟨$⟩ x) ∙ sumTable (map (f ⟨$⟩_) enumTable′) ≈ sumTable (map (f ⟨$⟩_) enumTable′)
        enumTable-complete′ f x =
          begin
            f$ x ∙ sumTable (map f$ enumTable′)                                            ≈⟨ ∙-cong refl (sumTable-permute (map f$ enumTable′) (Fin.swapIndices Fin.zero i)) ⟩
            f$ x ∙ sumTable (permute (Fin.swapIndices Fin.zero i) (map f$ enumTable′))     ≡⟨⟩
            f$ x ∙ (f$ (from (to x)) ∙ _)                                                  ≈⟨ ∙-cong refl (∙-cong (cong f (LeftInverse.left-inverse-of fromFin′ x)) refl) ⟩
            f$ x ∙ (f$ x ∙ _)                                                              ≈⟨ sym (assoc _ _ _) ⟩
            (f$ x ∙ f$ x) ∙ _                                                              ≈⟨ ∙-cong (idem _) refl ⟩
            f$ x ∙ _                                                                       ≈⟨ ∙-cong (cong f (≡.sym (LeftInverse.left-inverse-of fromFin′ x))) refl ⟩
            f$ (from (to x)) ∙ _                                                           ≡⟨⟩
            sumTable (permute (Fin.swapIndices Fin.zero i) (map f$ enumTable′))            ≈⟨ sym (sumTable-permute (map f$ enumTable′) (Fin.swapIndices Fin.zero i)) ⟩
            sumTable (map f$ enumTable′)                                                   ∎
          where
            i = to x
            f$ = f ⟨$⟩_

            open EqReasoning setoid

        sum/map-hom : ∀ {n} {a}{A : Set a} (f : A → S) (t : Table A n) → sum (List.map f (toList t)) ≡ sumTable (map f t)
        sum/map-hom f t =
          begin
            sum (List.map f (toList t))   ≡⟨ ≡.cong sum (Table.map-toList-hom f t) ⟩
            sum (toList (map f t))        ≡⟨ ≡.sym (sumTable-toList (map f t)) ⟩
            sumTable (map f t)            ∎
          where
            open ≡.Reasoning

        enumerate-complete′ : ∀ (f : ≡.setoid A ⟶ setoid) x → (f ⟨$⟩ x) ∙ sum (List.map (f ⟨$⟩_) enumerate′) ≈ sum (List.map (f ⟨$⟩_) enumerate′)
        enumerate-complete′ f x =
          begin
            f$ x ∙ sum (List.map f$ enumerate′)           ≡⟨⟩
            f$ x ∙ sum (List.map f$ (toList enumTable′))  ≡⟨ ≡.cong₂ _∙_ ≡.refl (sum/map-hom f$ enumTable′) ⟩
            f$ x ∙ sumTable (map f$ enumTable′)           ≈⟨ enumTable-complete′ f x ⟩
            sumTable (map f$ enumTable′)                  ≡⟨ ≡.sym (sum/map-hom f$ enumTable′) ⟩
            sum (List.map f$ enumerate′)                  ∎
          where
            f$ = f ⟨$⟩_
            open EqReasoning setoid

    private
      inhabited : ∀ {N} (i : Fin N) → ∃ λ n → N ≡ Nat.suc n
      inhabited Fin.zero = _ , ≡.refl
      inhabited (Fin.suc i) = _ , ≡.refl

    enumerate-complete : ∀ (f : ≡.setoid A ⟶ setoid) x → (f ⟨$⟩ x) ∙ sum (List.map (f ⟨$⟩_) enumerate) ≈ sum (List.map (f ⟨$⟩_) enumerate)
    enumerate-complete f x with inhabited (LeftInverse.to fromFin ⟨$⟩ x)
    enumerate-complete f x | n , p = {!!}
