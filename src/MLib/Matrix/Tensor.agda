open import MLib.Algebra.PropertyCode
open import MLib.Algebra.PropertyCode.Structures

module MLib.Matrix.Tensor {c ℓ} (struct : Struct bimonoidCode c ℓ) where

open import MLib.Prelude
open import MLib.Matrix.Core
open import MLib.Matrix.Equality struct
open import MLib.Matrix.Mul struct
open import MLib.Algebra.Operations struct

open Table using (head; tail; rearrange; fromList; toList; _≗_; replicate)
open Nat using () renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)

open FunctionProperties

open import MLib.Fin.Pieces.Simple

-- Tensor product

_⊠_ : ∀ {m n p q} → Matrix S m n → Matrix S p q → Matrix S (m *ℕ p) (n *ℕ q)
(A ⊠ B) i j =
  let i₁ , i₂ = fromPiece i
      j₁ , j₂ = fromPiece j
  in A i₁ j₁ *′ B i₂ j₂

private
  ≡⇒≡×≡×≡ :
    ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
    {i i′ : A} {j j′ : B} {k k′ : C} →
    (i , j , k) ≡ (i′ , j′ , k′) →
    i ≡ i′ × j ≡ j′ × k ≡ k′
  ≡⇒≡×≡×≡ = Σ.map id Σ.≡⇒≡×≡ ∘ Σ.≡⇒≡×≡

open _≃_

module _ ⦃ props : Has (associative on * ∷ []) ⦄ {m n p q r s} where

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

        i₁-eq , i₂-eq , i₃-eq = ≡⇒≡×≡×≡ (fromPiece-assoc m p r i≅i′)
        j₁-eq , j₂-eq , j₃-eq = ≡⇒≡×≡×≡ (fromPiece-assoc n q s j≅j′)

        open EqReasoning S.setoid
    in begin
      ((A ⊠ B) ⊠ C) i j                        ≡⟨⟩
      A i₁ j₁ *′ B i₂ j₂ *′ C i₃ j₃            ≈⟨ from props (associative on *) _ _ _ ⟩
      A i₁ j₁ *′ (B i₂ j₂ *′ C i₃ j₃)          ≈⟨ cong * (S.reflexive (≡.cong₂ A i₁-eq j₁-eq)) S.refl ⟩
      A i′₁ j′₁ *′ (B i₂ j₂ *′ C i₃ j₃)        ≈⟨ cong * S.refl (cong * (S.reflexive (≡.cong₂ B i₂-eq j₂-eq)) S.refl) ⟩
      A i′₁ j′₁ *′ (B i′₂ j′₂ *′ C i₃ j₃)      ≈⟨ cong * S.refl (cong * S.refl (S.reflexive (≡.cong₂ C i₃-eq j₃-eq))) ⟩
      A i′₁ j′₁ *′ (B i′₂ j′₂ *′ C i′₃ j′₃)    ≡⟨⟩
      (A ⊠ (B ⊠ C)) i′ j′                      ∎

⊠-cong : ∀ {m n m′ n′} {p q p′ q′} {A : Matrix S m n} {A′ : Matrix S m′ n′} {B : Matrix S p q} {B′ : Matrix S p′ q′} → A ≃ A′ → B ≃ B′ → (A ⊠ B) ≃ (A′ ⊠ B′)
⊠-cong A≃A′ B≃B′ with A≃A′ .m≡p | B≃B′ .m≡p | A≃A′ .n≡q | B≃B′ .n≡q
⊠-cong {A = A} {A′} {B} {B′} A≃A′ B≃B′ | ≡.refl | ≡.refl | ≡.refl | ≡.refl = lem
  where
  lem : (A ⊠ B) ≃ (A′ ⊠ B′)
  lem .m≡p = ≡.refl
  lem .n≡q = ≡.refl
  lem .equal ≅.refl ≅.refl = cong * (A≃A′ .equal ≅.refl ≅.refl) (B≃B′ .equal ≅.refl ≅.refl)

⊠-identityˡ :
  ⦃ props : Has (1# is leftIdentity for * ∷ []) ⦄ →
  ∀ {m n} (A : Matrix S m n) → 1● {1} ⊠ A ≃ A
⊠-identityˡ A .m≡p = Nat.*-identityˡ _
⊠-identityˡ A .n≡q = Nat.*-identityˡ _
⊠-identityˡ ⦃ props ⦄ A .equal {i} {i′} {j} {j′} i≅i′ j≅j′ =
  let i₁ , i₂ = fromPiece {1} i
      j₁ , j₂ = fromPiece {1} j
      -- x  : i₁ ≡ zero
      -- x′ : i₂ ≡ i′
      -- y  : j₁ ≡ zero
      -- y′ : j₂ ≡ j′
      x , x′ = Σ.≡⇒≡×≡ (fromPiece-1ˡ i i′ i≅i′)
      y , y′ = Σ.≡⇒≡×≡ (fromPiece-1ˡ j j′ j≅j′)

      open EqReasoning S.setoid
  in begin
    (1● {1} ⊠ A) i j           ≡⟨⟩
    1● {1} i₁ j₁     *′ A i₂ j₂ ≡⟨ ≡.cong₂ _*′_ (≡.cong₂ (1● {1}) x y) (≡.cong₂ A x′ y′) ⟩
    1● {1} zero zero *′ A i′ j′ ≡⟨⟩
    1′               *′ A i′ j′ ≈⟨ from props (1# is leftIdentity for *) _ ⟩
    A i′ j′ ∎

⊠-identityʳ :
  ⦃ props : Has (1# is rightIdentity for * ∷ []) ⦄ →
  ∀ {m n} (A : Matrix S m n) → A ⊠ 1● {1} ≃ A
⊠-identityʳ A .m≡p = Nat.*-identityʳ _
⊠-identityʳ A .n≡q = Nat.*-identityʳ _
⊠-identityʳ A .equal {i} {i′} {j} {j′} i≅i′ j≅j′ with Σ.≡⇒≡×≡ (fromPiece-1ʳ i i′ i≅i′) | Σ.≡⇒≡×≡ (fromPiece-1ʳ j j′ j≅j′)
⊠-identityʳ ⦃ props ⦄ A .equal {i} {i′} {j} {j′} i≅i′ j≅j′ | x , x′ | y , y′
  rewrite x | x′ | y | y′ = from props (1# is rightIdentity for *) _
