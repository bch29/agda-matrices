open import MLib.Algebra.PropertyCode
open import MLib.Algebra.PropertyCode.Structures

module MLib.Matrix.Tensor {c ℓ} (struct : Struct bimonoidCode c ℓ) where

open import MLib.Prelude
open import MLib.Matrix.Core
open import MLib.Algebra.Operations struct

import Data.Product as Product

open Algebra using (CommutativeMonoid)
open PropertyC
open Table using (head; tail; rearrange; fromList; toList; _≗_; replicate)
open Nat using (zero; suc) renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
open Fin using (zero; suc)
open import Function.Inverse using (_↔_; Inverse)
open import Function.Equality using (_⟶_; _⟨$⟩_)
import Data.Product.Relation.Pointwise.NonDependent as ΣR
open import Relation.Binary.HeterogeneousEquality as ≅ using (_≅_)

open OverBimonoid struct
open FunctionProperties

import MLib.Prelude.Fin.Pieces as P
open import MLib.Prelude.Fin.PiecesSimple

module _ (a b c : ℕ) where

  fromPiece³ : Fin (a *ℕ b *ℕ c) → Fin a × Fin b × Fin c
  fromPiece³ x =
    let ij , k = fromPiece x
        i , j = fromPiece ij
    in i , j , k

  fromPiece³-intoPiece³ : ∀ ijk → fromPiece³ (intoPiece³ ijk) ≡ ijk
  fromPiece³-intoPiece³ (i , j , k) =
    let i′ = proj₁ (fromPiece³ (intoPiece³ (i , j , k)))
        j′ = proj₁ (proj₂ (fromPiece³ (intoPiece³ (i , j , k))))
        k′ = proj₂ (proj₂ (fromPiece³ (intoPiece³ (i , j , k))))

        r , s = ΣR.≡⇒≡×≡ (asPiece .Inverse.left-inverse-of _)

        r′ : fromPiece (proj₁ (fromPiece (intoPiece³ (i , j , k)))) ≡ (i , j)
        r′ = ≡.trans (≡.cong fromPiece r) (asPiece .Inverse.left-inverse-of _)

        p , q = ΣR.≡⇒≡×≡ r′

    in ΣR.≡×≡⇒≡ (p , ΣR.≡×≡⇒≡ (q , s))

  intoPiece³-fromPiece³ : ∀ i → intoPiece³ (fromPiece³ i) ≡ i
  intoPiece³-fromPiece³ x =
    let i , j , k = fromPiece³ x

        open ≡.Reasoning

        lem : intoPiece (i , j) ≡ proj₁ (fromPiece x)
        lem = begin
          intoPiece (i , j)                                    ≡⟨⟩
          intoPiece {a} {b} (fromPiece (proj₁ (fromPiece x)))  ≡⟨ asPiece {a} {b} .Inverse.right-inverse-of _ ⟩
          proj₁ (fromPiece x)                                  ∎

    in begin
      intoPiece³ (fromPiece³ x)             ≡⟨⟩
      intoPiece (intoPiece (i , j) , k)     ≡⟨ ≡.cong intoPiece (ΣR.≡×≡⇒≡ (lem , ≡.refl)) ⟩
      intoPiece {a *ℕ b} {c} (fromPiece x)  ≡⟨ asPiece {a *ℕ b} {c} .Inverse.right-inverse-of _ ⟩
      x                                     ∎

  fromPiece³′ : Fin (a *ℕ (b *ℕ c)) → Fin a × Fin b × Fin c
  fromPiece³′ i =
    let i₁ , i₂₃ = fromPiece i
        i₂ , i₃ = fromPiece i₂₃
    in i₁ , i₂ , i₃

  fromPiece³′-intoPiece³′ : ∀ ijk → fromPiece³′ (intoPiece³′ ijk) ≡ ijk
  fromPiece³′-intoPiece³′ (i , j , k) =
    let i′ = proj₁ (fromPiece³′ (intoPiece³′ (i , j , k)))
        j′ = proj₁ (proj₂ (fromPiece³′ (intoPiece³′ (i , j , k))))
        k′ = proj₂ (proj₂ (fromPiece³′ (intoPiece³′ (i , j , k))))

        p , q = ΣR.≡⇒≡×≡ (asPiece .Inverse.left-inverse-of _)
        q′ = ≡.trans (≡.cong fromPiece q) (asPiece .Inverse.left-inverse-of _)

    in ΣR.≡×≡⇒≡ (p , q′)

  intoPiece-assoc′ : ∀ (ijk : Fin a × Fin b × Fin c) → ≡.subst Fin (Nat.*-assoc a b c) (intoPiece³ ijk) ≡ intoPiece³′ ijk
  intoPiece-assoc′ (i , j , k) = ≅.≅-to-≡ (≅.trans (≅.≡-subst-removable Fin (Nat.*-assoc a b c) _) (≅.sym (intoPiece-assoc i j k)))

  fromPiece-assoc : (i : Fin (a *ℕ b *ℕ c)) → fromPiece³ i ≡ fromPiece³′ (≡.subst Fin (Nat.*-assoc a b c) i)
  fromPiece-assoc i =
    begin
      fromPiece³ i                                                                ≡⟨ ≡.sym (fromPiece³′-intoPiece³′ _) ⟩
      fromPiece³′ (intoPiece³′ (fromPiece³ i))                                    ≡⟨ ≡.cong fromPiece³′ (≡.sym (intoPiece-assoc′ _)) ⟩
      fromPiece³′ (≡.subst Fin (Nat.*-assoc a b c) (intoPiece³ (fromPiece³ i)))   ≡⟨ ≡.cong (fromPiece³′ ∘ ≡.subst Fin (Nat.*-assoc a b c)) (intoPiece³-fromPiece³ _) ⟩
      fromPiece³′ (≡.subst Fin (Nat.*-assoc a b c) i)                             ∎
    where open ≡.Reasoning

module Defn {m n p q : ℕ} where
  -- Tensor product

  _⊠_ : Matrix S m n → Matrix S p q → Matrix S (m Nat.* p) (n Nat.* q)
  (A ⊠ B) i j =
    let i₁ , i₂ = fromPiece i
        j₁ , j₂ = fromPiece j
    in A i₁ j₁ *′ B i₂ j₂

open Defn using (_⊠_) public

module _ ⦃ props : Has (associative on * ∷ []) ⦄ {m n p q r s} where
  open _≃_

  ⊠-associative :
    (A : Matrix S m n) (B : Matrix S p q) (C : Matrix S r s) →
    (A ⊠ B) ⊠ C ≃ A ⊠ (B ⊠ C)
  ⊠-associative A B C .m≡p = Nat.*-assoc m p r
  ⊠-associative A B C .n≡q = Nat.*-assoc n q s
  ⊠-associative A B C .equal i j =
    let i₁ , i₂ , i₃ = fromPiece³ m p r i
        j₁ , j₂ , j₃ = fromPiece³ n q s j

        i′ = ≡.subst Fin (Nat.*-assoc m p r) i
        j′ = ≡.subst Fin (Nat.*-assoc n q s) j

        i′₁ , i′₂ , i′₃ = fromPiece³′ m p r i′
        j′₁ , j′₂ , j′₃ = fromPiece³′ n q s j′

        i₁-eq , i₂-eq , i₃-eq = Product.map id (ΣR.≡⇒≡×≡) (ΣR.≡⇒≡×≡ (fromPiece-assoc m p r i))
        j₁-eq , j₂-eq , j₃-eq = Product.map id (ΣR.≡⇒≡×≡) (ΣR.≡⇒≡×≡ (fromPiece-assoc n q s j))

        open EqReasoning S.setoid
    in begin
      ((A ⊠ B) ⊠ C) i j                    ≡⟨⟩
      A i₁ j₁ *′ B i₂ j₂ *′ C i₃ j₃         ≈⟨ from props (associative on *) _ _ _ ⟩
      A i₁ j₁ *′ (B i₂ j₂ *′ C i₃ j₃)       ≈⟨ cong * (S.reflexive (≡.cong₂ A i₁-eq j₁-eq)) S.refl ⟩
      A i′₁ j′₁ *′ (B i₂ j₂ *′ C i₃ j₃)     ≈⟨ cong * S.refl (cong * (S.reflexive (≡.cong₂ B i₂-eq j₂-eq)) S.refl) ⟩
      A i′₁ j′₁ *′ (B i′₂ j′₂ *′ C i₃ j₃)   ≈⟨ cong * S.refl (cong * S.refl (S.reflexive (≡.cong₂ C i₃-eq j₃-eq))) ⟩
      A i′₁ j′₁ *′ (B i′₂ j′₂ *′ C i′₃ j′₃) ≡⟨⟩
      (A ⊠ (B ⊠ C)) i′ j′                  ∎
