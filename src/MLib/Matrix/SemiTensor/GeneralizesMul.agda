open import MLib.Algebra.PropertyCode
open import MLib.Algebra.PropertyCode.Structures

module MLib.Matrix.SemiTensor.GeneralizesMul {c ℓ} (struct : Struct bimonoidCode c ℓ) where

open import MLib.Prelude
open import MLib.Matrix.Core
open import MLib.Matrix.Equality struct
open import MLib.Matrix.Mul struct
open import MLib.Matrix.Tensor struct
open import MLib.Matrix.SemiTensor.Core struct
open import MLib.Algebra.Operations struct

open Nat using () renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)

open import MLib.Fin.Parts.Simple

open import Data.Nat.LCM
open import Data.Nat.Divisibility

-- Semi-tensor product generalizes the usual matrix product

module _ ⦃ props : Has (1# is rightIdentity for * ∷ []) ⦄ where
  generalizes-⊗ : ∀ {m n o} (A : Matrix S m n) (B : Matrix S n o) → A ⋉ B ≃ A ⊗ B

  open _≃_

  module Zero {m o} (A : Matrix S m 0) (B : Matrix S 0 o) where
    generalizes-⊗′ : A ⋉ B ≃ A ⊗ B
    generalizes-⊗′ .m≡p = Nat.*-identityʳ m
    generalizes-⊗′ .n≡q = Nat.*-identityʳ o
    generalizes-⊗′ .equal _ _ = S.refl

  module Nonzero {m n o} (A : Matrix S m (suc n)) (B : Matrix S (suc n) o) where
    private
      t = lcm (suc n) (suc n) .proj₁
      t-lcm = lcm (suc n) (suc n) .proj₂

      open Defn t-lcm renaming (n∣t to sn∣t; t/n to t/sn; p∣t to sn∣t′; t/p to t/sn′)

      A′′-lem : A′′ A B ≃ A
      B′′-lem : B′′ A B ≃ B

    generalizes-⊗′ : A ⋉ B ≃ A ⊗ B
    generalizes-⊗′ = ⊗-cong-≃ _ _ _ _ A′′-lem B′′-lem

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

      A′′-lem = ≃-trans (≡-subst-≃₂ lem₁) (≃-trans (⊠-cong (≃-refl {A = A}) (1●-cong-≃ t/sn≡1)) (⊠-identityʳ ⦃ weaken props ⦄ A))
      B′′-lem = ≃-trans (≡-subst-≃₁ lem₂) (≃-trans (⊠-cong (≃-refl {A = B}) (1●-cong-≃ t/sn′≡1)) (⊠-identityʳ ⦃ weaken props ⦄ B))

  generalizes-⊗ {n = zero} = Zero.generalizes-⊗′
  generalizes-⊗ {n = suc n} = Nonzero.generalizes-⊗′
