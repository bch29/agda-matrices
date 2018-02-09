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

record IsFiniteSet {c ℓ} {A : Set c} (_≈_ : Rel A ℓ) (N : ℕ) : Set (c ⊔ˡ ℓ) where
  field
    isEquivalence : IsEquivalence _≈_

  setoid : Setoid _ _
  setoid = record { isEquivalence = isEquivalence }
  open IsEquivalence isEquivalence public

  OntoFin : ℕ → Set _
  OntoFin N = LeftInverse setoid (≡.setoid (Fin N))

  field
    ontoFin : OntoFin N

  open Table hiding (setoid)
  open List using ([]; _∷_)

  private
    enumTableAt : ∀ {N} → OntoFin N → Table A N
    enumTableAt ontoFin = tabulate (LeftInverse.from ontoFin ⟨$⟩_)

    enumerateAt : ∀ {N} → OntoFin N → List A
    enumerateAt ontoFin = Table.toList (enumTableAt ontoFin)

  enumTable : Table A N
  enumTable = enumTableAt ontoFin

  enumerate : List A
  enumerate = Table.toList enumTable

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

      enumTable-complete′′ : ∀ {N} (ontoFin′ : OntoFin N) (f : setoid ⟶ S.setoid) x → (f ⟨$⟩ x) ∙ sumTable (Table.map (f ⟨$⟩_) (enumTableAt ontoFin′)) ≈′ sumTable (Table.map (f ⟨$⟩_) (enumTableAt ontoFin′))
      enumTable-complete′′ ontoFin′ f x with inhabited (LeftInverse.to ontoFin′ ⟨$⟩ x)
      enumTable-complete′′ ontoFin′ f x | n , ≡.refl = enumTable-complete′ ontoFin′ f x

      sum/map-hom : ∀ {n} {a}{A : Set a} (f : A → S) (t : Table A n) → sum (List.map f (toList t)) ≡ sumTable (map f t)
      sum/map-hom f t =
        begin
          sum (List.map f (toList t))   ≡⟨ ≡.cong sum (Table.map-toList-hom f t) ⟩
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

record FiniteSet c ℓ : Set (sucˡ (c ⊔ˡ ℓ)) where
  field
    Carrier : Set c
    _≈_ : Rel Carrier ℓ
    N : ℕ
    isFiniteSet : IsFiniteSet _≈_ N

  open IsFiniteSet isFiniteSet public

record PointwiseFiniteSet {a} (A : Set a) c ℓ : Set (a ⊔ˡ sucˡ (c ⊔ˡ ℓ)) where
  field
    Carrier : A → Set c
    _≈_ : ∀ {x} → Rel (Carrier x) ℓ
    boundAt : A → ℕ
    finiteAt : ∀ x → IsFiniteSet {A = Carrier x} _≈_ (boundAt x)

  module _ x where
    open IsFiniteSet (finiteAt x) public
