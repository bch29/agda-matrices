open import MLib.Prelude
open import MLib.Algebra.PropertyCode
open import MLib.Algebra.PropertyCode.Structures

module MLib.Matrix.Plus {c ℓ} (struct : Struct bimonoidCode c ℓ) {m n : ℕ} where

open import MLib.Matrix.Core
open import MLib.Matrix.Equality struct

open FunctionProperties

-- Pointwise addition --

infixl 6 _⊕_

_⊕_ : Matrix S m n → Matrix S m n → Matrix S m n
(A ⊕ B) i j = A i j ⟨ + ⟩ B i j

⊕-cong : Congruent₂ _⊕_
⊕-cong p q = λ i j → S.cong + (p i j) (q i j)

⊕-assoc : ⦃ props : Has₁ (associative on +) ⦄ → Associative _⊕_
⊕-assoc ⦃ props ⦄ A B C i j = from props (associative on +) (A i j) (B i j) (C i j)

0● : Matrix S m n
0● _ _ = ⟦ 0# ⟧

⊕-identityˡ : ⦃ props : Has₁ (0# is leftIdentity for +) ⦄ → LeftIdentity 0● _⊕_
⊕-identityˡ ⦃ props ⦄ A i j = from props (0# is leftIdentity for +) (A i j)

⊕-identityʳ : ⦃ props : Has₁ (0# is rightIdentity for +) ⦄ → RightIdentity 0● _⊕_
⊕-identityʳ ⦃ props ⦄ A i j = from props (0# is rightIdentity for +) (A i j)

⊕-comm : ⦃ props : Has₁ (commutative on +) ⦄ → Commutative _⊕_
⊕-comm ⦃ props ⦄ A B i j = from props (commutative on +) (A i j) (B i j)
