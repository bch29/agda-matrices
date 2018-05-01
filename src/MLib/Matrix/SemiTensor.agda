open import MLib.Algebra.PropertyCode
open import MLib.Algebra.PropertyCode.Structures

module MLib.Matrix.SemiTensor {c ℓ} (struct : Struct bimonoidCode c ℓ) where

open import MLib.Prelude
open import MLib.Matrix.Core
open import MLib.Matrix.Mul struct
open import MLib.Matrix.Tensor struct
open import MLib.Algebra.Operations struct

open Table using (head; tail; rearrange; fromList; toList; _≗_; replicate)
open Nat using () renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)

open OverBimonoid struct
open FunctionProperties

open import MLib.Fin.Pieces.Simple

open import Data.Nat.LCM
open import Data.Nat.Divisibility

chunkVec : ∀ {m n} → Table S (m *ℕ n) → Table (Table S n) m
chunkVec {m} {n} t .lookup i .lookup j = lookup t (intoPiece (i , j))

-- Case 1 of semi-tensor inner product of vectors

_⋉ᵥ₁_ : ∀ {n t} → Table S (t *ℕ n) → Table S t → Table S n
(_⋉ᵥ₁_ {n} {t} X Y) .lookup i = ∑[ k < t ] (X′ .lookup k .lookup i *′ Y .lookup k)
  where X′ = chunkVec {t} X

-- Case 2 of semi-tensor inner product of vector

_⋉ᵥ₂_ : ∀ {n s} → Table S s → Table S (s *ℕ n) → Table S n
(_⋉ᵥ₂_ {n} {s} X Y) .lookup i = ∑[ k < s ] (X .lookup k *′ Y′ .lookup k .lookup i)
  where Y′ = chunkVec {s} Y

module Defn {n p t : ℕ} (lcm : LCM n p t) where
  -- Left semi-Tensor product

  n∣t = LCM.commonMultiple lcm .proj₁
  p∣t = LCM.commonMultiple lcm .proj₂

  t/n = quotient n∣t
  t/p = quotient p∣t

  Iₜₙ = 1● {t/n}
  Iₜₚ = 1● {t/p}

  module _ where
    open ≡.Reasoning

    abstract
      lem₁ : n *ℕ t/n ≡ t
      lem₁ = begin
        n *ℕ t/n ≡⟨ Nat.*-comm n _ ⟩
        t/n *ℕ n ≡⟨ ≡.sym (_∣_.equality n∣t) ⟩
        t ∎

      lem₂ : p *ℕ t/p ≡ t
      lem₂ = begin
        p *ℕ t/p ≡⟨ Nat.*-comm p _ ⟩
        t/p *ℕ p ≡⟨ ≡.sym (_∣_.equality p∣t) ⟩
        t ∎

  module _ {m q} (A : Matrix S m n) (B : Matrix S p q) where
    A′ = A ⊠ Iₜₙ
    B′ = B ⊠ Iₜₚ
    A′′ = ≡.subst (Matrix S (m *ℕ t/n)) {y = t} lem₁ A′
    B′′ = ≡.subst (λ h → Matrix S h (q *ℕ t/p)) {y = t} lem₂ B′

    stp : Matrix S (m *ℕ t/n) (q *ℕ t/p)
    stp = A′′ ⊗ B′′

infixl 7 _⋉_

_⋉_ : ∀ {n m p q} → Matrix S m n → Matrix S p q → Matrix S _ _
_⋉_ {n} {m} {p} {q} = Defn.stp {n} {p} (lcm n p .proj₂)

module _ ⦃ props : Has (1# is rightIdentity for * ∷ associative on * ∷ []) ⦄ {m n o} (A : Matrix S m (suc n)) (B : Matrix S (suc n) o) where
  open _≃_

  private
    t = lcm (suc n) (suc n) .proj₁
    t-lcm = lcm (suc n) (suc n) .proj₂

    open Defn t-lcm renaming (n∣t to sn∣t; t/n to t/sn; p∣t to sn∣t′; t/p to t/sn′)

    A′′-lem : A′′ A B ≃ A
    B′′-lem : B′′ A B ≃ B

  generalizes-⊗ : A ⋉ B ≃ A ⊗ B
  generalizes-⊗ = ⊗-cong-≃ _ _ _ _ A′′-lem B′′-lem

  private
    abstract
      lcm-n-n : ∀ {n t} → LCM n n t → t ≡ n
      lcm-n-n {n} isLcm =
        let t∣n = LCM.least isLcm (∣-refl , ∣-refl)
            n∣t = LCM.commonMultiple isLcm .proj₁
        in ∣-antisym t∣n n∣t

      quotient-n-n : ∀ {n} (p : suc n ∣ suc n) → quotient p ≡ 1
      quotient-n-n (divides q equality) = Nat.*-cancelʳ-≡ q 1 (≡.sym (≡.trans (≡.cong suc (Nat.+-identityʳ _)) equality))

      quotient-subst : ∀ {n p q} (n∣p : n ∣ p) (p≡q : p ≡ q) → quotient n∣p ≡ quotient (≡.subst (λ h → n ∣ h) p≡q n∣p)
      quotient-subst n∣p ≡.refl = ≡.refl

      t≡sn : t ≡ suc n
      t≡sn = lcm-n-n t-lcm

      t/sn≡1 : t/sn ≡ 1
      t/sn≡1 =
        begin
          t/sn ≡⟨ quotient-subst sn∣t t≡sn ⟩
          quotient (≡.subst (λ h → suc n ∣ h) t≡sn sn∣t) ≡⟨ quotient-n-n (≡.subst (λ h → suc n ∣ h) t≡sn sn∣t) ⟩
          1 ∎
        where open ≡.Reasoning

      t/sn′≡1 : t/sn′ ≡ 1
      t/sn′≡1 =
        begin
          t/sn′ ≡⟨ quotient-subst sn∣t′ t≡sn ⟩
          quotient (≡.subst (λ h → suc n ∣ h) t≡sn sn∣t′) ≡⟨ quotient-n-n (≡.subst (λ h → suc n ∣ h) t≡sn sn∣t′) ⟩
          1 ∎
        where open ≡.Reasoning

      lhs≡m : m *ℕ t/sn ≡ m
      lhs≡m =
        begin
          m *ℕ t/sn ≡⟨ ≡.cong₂ _*ℕ_ (≡.refl {x = m}) t/sn≡1 ⟩
          m *ℕ 1 ≡⟨ Nat.*-identityʳ _ ⟩
          m ∎
        where open ≡.Reasoning

      rhs≡o : o *ℕ t/sn′ ≡ o
      rhs≡o =
        begin
          o *ℕ t/sn′ ≡⟨ ≡.cong₂ _*ℕ_ (≡.refl {x = o}) t/sn′≡1 ⟩
          o *ℕ 1 ≡⟨ Nat.*-identityʳ _ ⟩
          o ∎
        where open ≡.Reasoning

    A′′-lem = ≃-trans (≡-subst-≃₂ lem₁) (≃-trans (⊠-cong (≃-refl {A = A}) (1●-cong-≃ t/sn≡1)) (⊠-identityʳ ⦃ narrow props ⦄ A))
    B′′-lem = ≃-trans (≡-subst-≃₁ lem₂) (≃-trans (⊠-cong (≃-refl {A = B}) (1●-cong-≃ t/sn′≡1)) (⊠-identityʳ ⦃ narrow props ⦄ B))
