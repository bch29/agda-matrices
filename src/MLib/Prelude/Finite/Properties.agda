open import MLib.Prelude.Finite

module MLib.Prelude.Finite.Properties {c ℓ} (finiteSet : FiniteSet c ℓ) where

open import MLib.Prelude.FromStdlib
import MLib.Prelude.Fin as Fin
open Fin using (Fin)

import Relation.Binary as B

open import Function.LeftInverse using (LeftInverse; _↞_) renaming (_∘_ to _ⁱ∘_)
open import Function.Inverse using (Inverse; _↔_)
open import Function.Equality as FE using (_⟶_; _⟨$⟩_; cong)

open Algebra using (IdempotentCommutativeMonoid)

open Table hiding (setoid)
open List using ([]; _∷_)


open FiniteSet finiteSet renaming (Carrier to A)

private
  enumₜAt : ∀ {N} → OntoFin N → Table A N
  enumₜAt = tabulate ∘ _⟨$⟩_ ∘ LeftInverse.from

module _ {c ℓ} (icMonoid : IdempotentCommutativeMonoid c ℓ) where
  module S = IdempotentCommutativeMonoid icMonoid
  open S using (_∙_; ∙-cong) renaming (Carrier to S; _≈_ to _≈′_)
  open import Algebra.Operations.CommutativeMonoid S.commutativeMonoid
  open import Algebra.Properties.CommutativeMonoid S.commutativeMonoid

  foldMap : (A → S) → S
  foldMap f = sumₜ (Table.map f enumₜ)

  foldMap-cong : ∀ {f g} → (∀ x → f x ≈′ g x) → foldMap f ≈′ foldMap g
  foldMap-cong p = sumₜ-cong (p ∘ lookup enumₜ)

  private
    inhabited : ∀ {N} (i : Fin N) → ∃ λ n → N ≡ Nat.suc n
    inhabited Fin.zero = _ , ≡.refl
    inhabited (Fin.suc i) = _ , ≡.refl


  -- Folding with a constant function produces the constant.

  foldMap-const : ∀ {x} → x ∙ foldMap (λ _ → x) ≈′ x
  foldMap-const {x} =
    begin
      x ∙ foldMap (λ _ → x)                  ≡⟨⟩
      x ∙ sumₜ (Table.map (λ _ → x) enumₜ)   ≡⟨⟩
      x ∙ sumₜ (Table.replicate {N} x)       ≡⟨⟩
      sumₜ (Table.replicate {Nat.suc N} x)   ≈⟨ sumₜ-idem-replicate N (S.idem x) ⟩
      x                                      ∎
    where open EqReasoning S.setoid

  private
    module _ {n : ℕ} (ontoFin′ : OntoFin (Nat.suc n)) where
      from = LeftInverse.from ontoFin′ ⟨$⟩_
      to = LeftInverse.to ontoFin′ ⟨$⟩_
      from-to = LeftInverse.left-inverse-of ontoFin′

      enumₜ′ : Table A (Nat.suc n)
      enumₜ′ = enumₜAt ontoFin′

      ap : setoid ⟶ S.setoid → A → S
      ap = _⟨$⟩_

      enumₜ-complete′ : ∀ (func : setoid ⟶ S.setoid) x → (func ⟨$⟩ x) ∙ sumₜ (map (ap func) enumₜ′) ≈′ sumₜ (map (ap func) enumₜ′)
      enumₜ-complete′ func x =
        begin
          f x ∙ sumₜ (map f enumₜ′)                                         ≈⟨ ∙-cong S.refl (sumₜ-permute (map f enumₜ′) (Fin.swapIndices Fin.zero i)) ⟩
          f x ∙ sumₜ (permute (Fin.swapIndices Fin.zero i) (map f enumₜ′))  ≡⟨⟩
          f x ∙ (f (from (to x)) ∙ _)                                       ≈⟨ ∙-cong S.refl (∙-cong (cong func (from-to _)) S.refl) ⟩
          f x ∙ (f x ∙ _)                                                   ≈⟨ S.sym (S.assoc _ _ _) ⟩
          (f x ∙ f x) ∙ _                                                   ≈⟨ ∙-cong (S.idem _) S.refl ⟩
          f x ∙ _                                                           ≈⟨ ∙-cong (cong func (sym (from-to _))) S.refl ⟩
          f (from (to x)) ∙ _                                               ≡⟨⟩
          sumₜ (permute (Fin.swapIndices Fin.zero i) (map f enumₜ′))        ≈⟨ S.sym (sumₜ-permute (map f enumₜ′) (Fin.swapIndices Fin.zero i)) ⟩
          sumₜ (map f enumₜ′)                                               ∎
        where
          f = ap func
          i = to x

          open EqReasoning S.setoid

  private
    enumₜ-complete′′ :
      ∀ {N} (ontoFin′ : OntoFin N) (f : setoid ⟶ S.setoid) x
      → (f ⟨$⟩ x) ∙ sumₜ (Table.map (f ⟨$⟩_) (enumₜAt ontoFin′))
        ≈′ sumₜ (Table.map (f ⟨$⟩_) (enumₜAt ontoFin′))
    enumₜ-complete′′ ontoFin′ f x with inhabited (LeftInverse.to ontoFin′ ⟨$⟩ x)
    enumₜ-complete′′ ontoFin′ f x | n , ≡.refl = enumₜ-complete′ ontoFin′ f x

    sum/map-hom : ∀ {n} {a}{A : Set a} (f : A → S) (t : Table A n) → sumₗ (List.map f (toList t)) ≡ sumₜ (map f t)
    sum/map-hom f t =
      begin
        sumₗ (List.map f (toList t))   ≡⟨ ≡.cong sumₗ (Table.map-toList-hom t) ⟩
        sumₗ (toList (map f t))        ≡⟨ ≡.sym (sumₜ-toList (map f t)) ⟩
        sumₜ (map f t)                 ∎
      where
        open ≡.Reasoning


  -- Enumeration is complete: in any idempotent commutative monoid, adding one
  -- more element to the sum won't change it. In particular, this works in the
  -- powerset monoid, where 'f' is the singleton at its argument and addition
  -- is set union. This shows that every member of 'A' is present in the
  -- enumeration (even though the powerset monoid is quite difficult to
  -- implement in Agda so this proof is not present).

  enumₜ-complete : ∀ f x → (f ⟨$⟩ x) ∙ foldMap (f ⟨$⟩_) ≈′ foldMap (f ⟨$⟩_)
  enumₜ-complete = enumₜ-complete′′ ontoFin

  enumₗ-complete : ∀ (f : setoid ⟶ S.setoid) x → (f ⟨$⟩ x) ∙ sumₗ (List.map (f ⟨$⟩_) enumₗ) ≈′ sumₗ (List.map (f ⟨$⟩_) enumₗ)
  enumₗ-complete func x =
    begin
      f x ∙ sumₗ (List.map f enumₗ)           ≡⟨⟩
      f x ∙ sumₗ (List.map f (toList enumₜ))  ≡⟨ ≡.cong₂ _∙_ ≡.refl (sum/map-hom f enumₜ) ⟩
      f x ∙ sumₜ (map f enumₜ)                ≈⟨ enumₜ-complete func x ⟩
      sumₜ (map f enumₜ)                      ≡⟨ ≡.sym (sum/map-hom f enumₜ) ⟩
      sumₗ (List.map f enumₗ)                 ∎
    where
      f = func ⟨$⟩_
      open EqReasoning S.setoid


-- A finite set can be strictly totally ordered by its elements' indices

Ixorder : B.StrictTotalOrder _ _ _
Ixorder = record
  { _≈_ = _≈_
  ; _<_ = λ x y → toIx x Fin.< toIx y
  ; isStrictTotalOrder = record
    { isEquivalence = isEquivalence
    ; trans = Fin.<-trans
    ; compare = compare
    }
  }
  where
  compare : Trichotomous _≈_ (λ x y → toIx x Fin.< toIx y)
  compare x y with B.StrictTotalOrder.compare (Fin.<-strictTotalOrder N) (toIx x) (toIx y)
  compare x y | B.tri< a ¬b ¬c = B.tri< a (¬b ∘ cong (LeftInverse.to ontoFin)) ¬c
  compare x y | B.tri≈ ¬a b ¬c = B.tri≈ ¬a (LeftInverse.injective ontoFin b) ¬c
  compare x y | B.tri> ¬a ¬b c = B.tri> ¬a (¬b ∘ cong (LeftInverse.to ontoFin)) c


-- Equality between members of a finite set is decidable.

_≟_ : B.Decidable _≈_
_≟_ = B.StrictTotalOrder._≟_ Ixorder
