module MLib.Matrix.Core where

open import MLib.Prelude
open import MLib.Algebra.PropertyCode
open import MLib.Algebra.PropertyCode.Structures

open import Data.Vec.Relation.Pointwise.Inductive using (Pointwise; []; _∷_)

open Algebra using (CommutativeMonoid)

open PropertyC

Matrix : ∀ {a} → Set a → ℕ → ℕ → Set a
Matrix A m n = Fin m → Fin n → A

module OverBimonoid {c ℓ} (struct : Struct bimonoidCode c ℓ) where
  module S = Struct struct renaming (Carrier to S; _≈_ to _≈′_)
  open S using (S; _≈′_; _⟨_⟩_; ⟦_⟧; Has; HasList; HasEach; use; from; subStruct; inSubStruct; get; cong) public

  module _ {m n} where

    -- Pointwise equality --

    _≈_ : Rel (Matrix S m n) _
    A ≈ B = ∀ i j → A i j ≈′ B i j

    isEquivalence : IsEquivalence _≈_
    isEquivalence = record { Proofs } where
      module Proofs where
        refl : Reflexive _≈_
        refl _ _ = S.refl

        sym : Symmetric _≈_
        sym p = λ i j → S.sym (p i j)

        trans : Transitive _≈_
        trans p q = λ i j → S.trans (p i j) (q i j)

    setoid : Setoid _ _
    setoid = record { isEquivalence = isEquivalence }

    module FunctionProperties = Algebra.FunctionProperties _≈_

