module MLib.Matrix.Core where

open import MLib.Prelude
open import MLib.Algebra.PropertyCode
open import MLib.Algebra.PropertyCode.Structures

import Relation.Binary.Indexed as I

Matrix : ∀ {a} → Set a → ℕ → ℕ → Set a
Matrix A m n = Fin m → Fin n → A

module _ {a} (A : Set a) where
  row : ∀ {m n} → Fin m → Matrix A m n → Table A n
  row i M .lookup j = M i j

  col : ∀ {m n} → Fin n → Matrix A m n → Table A m
  col j M .lookup i = M i j

module OverBimonoid {c ℓ} (struct : Struct bimonoidCode c ℓ) where
  module S = Struct struct renaming (Carrier to S; _≈_ to _≈′_)
  open S hiding (isEquivalence; setoid; refl; sym; trans) public

  module _ {m n} where

    -- Pointwise equality --

    infix 4 _≈_

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

  -- Size-heterogeneous pointwise equality

  infix 4 _≃_

  record _≃_ {m n p q} (A : Matrix S m n) (B : Matrix S p q) : Set (c ⊔ˡ ℓ) where
    field
      m≡p : m ≡ p
      n≡q : n ≡ q
      equal : ∀ {i i′ j j′} → i ≅ i′ → j ≅ j′ → A i j ≈′ B i′ j′

  open _≃_

  ≃-refl : ∀ {m n} {A : Matrix S m n} → A ≃ A
  ≃-refl .m≡p = ≡.refl
  ≃-refl .n≡q = ≡.refl
  ≃-refl .equal ≅.refl ≅.refl = S.refl

  ≃-trans :
    ∀ {m n p q r s} {A : Matrix S m n} {B : Matrix S p q} {C : Matrix S r s} →
    A ≃ B → B ≃ C → A ≃ C
  ≃-trans x y .m≡p = ≡.trans (x .m≡p) (y .m≡p)
  ≃-trans x y .n≡q = ≡.trans (x .n≡q) (y .n≡q)
  ≃-trans {m} {n} {p} {q} {r} {s} x y .equal i≅i′′ j≅j′′ =
    let i≅i′ = ≅.sym (≅.≡-subst-removable Fin (x .m≡p) _)
        i′≅i′′ = ≅.trans (≅.sym i≅i′) i≅i′′
        j≅j′ = ≅.sym (≅.≡-subst-removable Fin (x .n≡q) _)
        j′≅j′′ = ≅.trans (≅.sym j≅j′) j≅j′′
    in S.trans (x .equal i≅i′ j≅j′) (y .equal i′≅i′′ j′≅j′′)

  ≃-sym :
    ∀ {m n p q} {A : Matrix S m n} {B : Matrix S p q} →
    A ≃ B → B ≃ A
  ≃-sym A≃B .m≡p = ≡.sym (A≃B .m≡p)
  ≃-sym A≃B .n≡q = ≡.sym (A≃B .n≡q)
  ≃-sym A≃B .equal i≅i′ j≅j′ = S.sym (A≃B .equal (≅.sym i≅i′) (≅.sym j≅j′))

  ≃-setoid : I.Setoid (ℕ × ℕ) _ _
  ≃-setoid = record
    { Carrier = uncurry (Matrix S)
    ; _≈_ = _≃_
    ; isEquivalence = record
      { refl = ≃-refl
      ; sym = ≃-sym
      ; trans = ≃-trans
      }
    }

  ≡-subst-≃₁ : ∀ {m n p} {A : Matrix S m n} (m≡p : m ≡ p) → ≡.subst (λ h → Matrix S h n) m≡p A ≃ A
  ≡-subst-≃₁ ≡.refl = ≃-refl

  ≡-subst-≃₂ : ∀ {m n q} {A : Matrix S m n} (n≡q : n ≡ q) → ≡.subst (Matrix S m) n≡q A ≃ A
  ≡-subst-≃₂ ≡.refl = ≃-refl
