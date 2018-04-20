open import MLib.Algebra.PropertyCode
open import MLib.Algebra.PropertyCode.Structures

module MLib.Matrix.Plus {c ℓ} (struct : Struct bimonoidCode c ℓ) where

open import MLib.Prelude
open import MLib.Matrix.Core

open Algebra using (CommutativeMonoid)
open PropertyC
open OverBimonoid struct
open FunctionProperties

module _ {m n} where
  -- Pointwise addition --

  _⊕_ : Matrix S m n → Matrix S m n → Matrix S m n
  (A ⊕ B) i j = A i j ⟨ + ⟩ B i j

  ⊕-cong : Congruent₂ _⊕_
  ⊕-cong p q = λ i j → S.cong + (p i j) (q i j)

  assoc : ⦃ props : Has (associative on +) ⦄ → Associative _⊕_
  assoc ⦃ props ⦄ A B C i j = from props (associative on +) (A i j) (B i j) (C i j)

  0● : Matrix S m n
  0● _ _ = ⟦ 0# ⟧

  identityˡ : ⦃ props : Has (0# is leftIdentity for +) ⦄ → LeftIdentity 0● _⊕_
  identityˡ ⦃ props ⦄ A i j = from props (0# is leftIdentity for +) (A i j)

  identityʳ : ⦃ props : Has (0# is rightIdentity for +) ⦄ → RightIdentity 0● _⊕_
  identityʳ ⦃ props ⦄ A i j = from props (0# is rightIdentity for +) (A i j)

  comm : ⦃ props : Has (commutative on +) ⦄ → Commutative _⊕_
  comm ⦃ props ⦄ A B i j = from props (commutative on +) (A i j) (B i j)
