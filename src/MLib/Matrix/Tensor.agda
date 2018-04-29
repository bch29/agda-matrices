open import MLib.Algebra.PropertyCode
open import MLib.Algebra.PropertyCode.Structures

module MLib.Matrix.Tensor {c ℓ} (struct : Struct bimonoidCode c ℓ) where

open import MLib.Prelude
open import MLib.Matrix.Core
open import MLib.Algebra.Operations struct

open Table using (head; tail; rearrange; fromList; toList; _≗_; replicate)
open Nat using () renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)

open OverBimonoid struct
open FunctionProperties

open import MLib.Fin.PiecesSimple

-- Tensor product

_⊠_ : ∀ {m n p q} → Matrix S m n → Matrix S p q → Matrix S (m *ℕ p) (n *ℕ q)
(A ⊠ B) i j =
  let i₁ , i₂ = fromPiece i
      j₁ , j₂ = fromPiece j
  in A i₁ j₁ *′ B i₂ j₂

module _ ⦃ props : Has (associative on * ∷ []) ⦄ {m n p q r s} where
  open _≃_

  ⊠-associative :
    (A : Matrix S m n) (B : Matrix S p q) (C : Matrix S r s) →
    (A ⊠ B) ⊠ C ≃ A ⊠ (B ⊠ C)
  ⊠-associative A B C .m≡p = Nat.*-assoc m p r
  ⊠-associative A B C .n≡q = Nat.*-assoc n q s
  ⊠-associative A B C .equal {i} {i′} {j} {j′} i≅i′ j≅j′ =
    let i₁ , i₂ , i₃ = fromPiece³ m p r i
        j₁ , j₂ , j₃ = fromPiece³ n q s j

        i′₁ , i′₂ , i′₃ = fromPiece³′ m p r i′
        j′₁ , j′₂ , j′₃ = fromPiece³′ n q s j′

        i₁-eq , i₂-eq , i₃-eq = Σ.map id (Σ.≡⇒≡×≡) (Σ.≡⇒≡×≡ (fromPiece-assoc m p r i≅i′))
        j₁-eq , j₂-eq , j₃-eq = Σ.map id (Σ.≡⇒≡×≡) (Σ.≡⇒≡×≡ (fromPiece-assoc n q s j≅j′))

        open EqReasoning S.setoid
    in begin
      ((A ⊠ B) ⊠ C) i j                        ≡⟨⟩
      A i₁ j₁ *′ B i₂ j₂ *′ C i₃ j₃            ≈⟨ from props (associative on *) _ _ _ ⟩
      A i₁ j₁ *′ (B i₂ j₂ *′ C i₃ j₃)          ≈⟨ cong * (S.reflexive (≡.cong₂ A i₁-eq j₁-eq)) S.refl ⟩
      A i′₁ j′₁ *′ (B i₂ j₂ *′ C i₃ j₃)        ≈⟨ cong * S.refl (cong * (S.reflexive (≡.cong₂ B i₂-eq j₂-eq)) S.refl) ⟩
      A i′₁ j′₁ *′ (B i′₂ j′₂ *′ C i₃ j₃)      ≈⟨ cong * S.refl (cong * S.refl (S.reflexive (≡.cong₂ C i₃-eq j₃-eq))) ⟩
      A i′₁ j′₁ *′ (B i′₂ j′₂ *′ C i′₃ j′₃)    ≡⟨⟩
      (A ⊠ (B ⊠ C)) i′ j′                      ∎
