open import MLib.Algebra.PropertyCode
open import MLib.Algebra.PropertyCode.Structures

module MLib.Matrix.Mul {c ℓ} (struct : Struct bimonoidCode c ℓ) where

open import MLib.Prelude
open import MLib.Matrix.Core
open import MLib.Matrix.Equality struct
open import MLib.Matrix.Plus struct
open import MLib.Algebra.Operations struct

open FunctionProperties
open Table using (head; tail; rearrange; fromList; toList; _≗_)

1● : ∀ {n} → Matrix S n n
1● i j with i Fin.≟ j
1● i j | yes _ = 1′
1● i j | no  _ = 0′

infixl 7 _⊗_

_⊗_ : ∀ {m n o} → Matrix S m n → Matrix S n o → Matrix S m o
_⊗_ {n = n} A B i k = ∑[ j < n ] (A i j *′ B j k)

⊗-cong : ∀ {m n o} {A A′ : Matrix S m n} {B B′ : Matrix S n o} → A ≈ A′ → B ≈ B′ → (A ⊗ B) ≈ (A′ ⊗ B′)
⊗-cong A≈A′ B≈B′ i k = sumₜ-cong (λ j → cong * (A≈A′ i j) (B≈B′ j k))

open _≃_

1●-cong-≃ : ∀ {m n} → m ≡ n → 1● {m} ≃ 1● {n}
1●-cong-≃ ≡.refl = ≃-refl

⊗-cong-≃ : ∀ {m n o m′ n′ o′} (A : Matrix S m n) (B : Matrix S n o) (A′ : Matrix S m′ n′) (B′ : Matrix S n′ o′) → A ≃ A′ → B ≃ B′ → (A ⊗ B) ≃ (A′ ⊗ B′)
⊗-cong-≃ A B A′ B′ p q .m≡p = p .m≡p
⊗-cong-≃ A B A′ B′ p q .n≡q = q .n≡q
⊗-cong-≃ {n = n} {n′ = n′} A B A′ B′ p q .equal {i} {i′} {k} {k′} i≅i′ k≅k′ =
  begin
    (A  ⊗ B ) i k                       ≡⟨⟩
    ∑[ j  < n  ] (A  i  j  *′ B  j  k)  ≈⟨ sumₜ-cong′ {n} {n′} (p .n≡q , λ _ _ j≅j′ → cong * (p .equal i≅i′ j≅j′) (q .equal j≅j′ k≅k′)) ⟩
    ∑[ j′ < n′ ] (A′ i′ j′ *′ B′ j′ k′) ≡⟨⟩
    (A′ ⊗ B′) i′ k′                     ∎
  where
    open EqReasoning S.setoid

⊗-assoc :
  ⦃ props : Has ( * ⟨ distributesOverˡ ⟩ₚ +
                ∷ * ⟨ distributesOverʳ ⟩ₚ +
                ∷ associative on *
                ∷ 0# is leftZero for *
                ∷ 0# is rightZero for *
                ∷ 0# is leftIdentity for +
                ∷ associative on +
                ∷ commutative on +
                ∷ []) ⦄
  → ∀ {m n p q} (A : Matrix S m n) (B : Matrix S n p) (C : Matrix S p q)
  → ((A ⊗ B) ⊗ C) ≈ (A ⊗ (B ⊗ C))
⊗-assoc ⦃ props ⦄ {m} {n} {p} {q} A B C i l =
  begin
    ((A ⊗ B) ⊗ C) i l                                    ≡⟨⟩
    ∑[ k < p ] (∑[ j < n ] (A i j *′ B j k) *′ C k l)     ≈⟨ sumₜ-cong {p} (λ k → sumDistribʳ ⦃ weaken props ⦄ {n} _ _) ⟩
    ∑[ k < p ] (∑[ j < n ] ((A i j *′ B j k) *′ C k l))   ≈⟨ sumₜ-cong {p} (λ k → sumₜ-cong {n} (λ j → from props (associative on *) _ _ _)) ⟩
    ∑[ k < p ] (∑[ j < n ] (A i j *′ (B j k *′ C k l)))   ≈⟨ ∑-comm ⦃ weaken props ⦄ p n _ ⟩
    ∑[ j < n ] (∑[ k < p ] (A i j *′ (B j k *′ C k l)))   ≈⟨ sumₜ-cong {n} (λ j → S.sym (sumDistribˡ ⦃ weaken props ⦄ {p} _ _)) ⟩
    ∑[ j < n ] (A i j *′ ∑[ k < p ] (B j k *′ C k l))     ≡⟨⟩
    (A ⊗ (B ⊗ C)) i l                                    ∎
  where open EqReasoning S.setoid

1-*-comm :
  ⦃ props : Has (1# is leftIdentity for * ∷ 1# is rightIdentity for * ∷ 0# is leftZero for * ∷ 0# is rightZero for * ∷ []) ⦄ →
  ∀ {n} (i j : Fin n) x → 1● i j *′ x ≈′ x *′ 1● i j
1-*-comm i j x with i Fin.≟ j
1-*-comm ⦃ props ⦄ i j x | yes p = S.trans (from props (1# is leftIdentity for *) _) (S.sym (from props (1# is rightIdentity for *) _))
1-*-comm ⦃ props ⦄ i j x | no ¬p = S.trans (from props (0# is leftZero for *) _) (S.sym (from props (0# is rightZero for *) _))

1-selectˡ :
  ⦃ props : Has (1# is leftIdentity for * ∷ 0# is leftZero for * ∷ []) ⦄ →
  ∀ {n} (i : Fin n) t j → (1● i j *′ lookup t j) ≈′ lookup (Table.select 0′ i t) j
1-selectˡ i t j with i Fin.≟ j | j Fin.≟ i
1-selectˡ ⦃ props ⦄ i t .i | yes ≡.refl | yes q = from props (1# is leftIdentity for *) _
1-selectˡ .j t j | yes ≡.refl | no ¬q = ⊥-elim (¬q ≡.refl)
1-selectˡ i t .i | no ¬p | yes ≡.refl = ⊥-elim (¬p ≡.refl)
1-selectˡ ⦃ props ⦄ i t j | no _ | no ¬p = from props (0# is leftZero for *) _


1-selectʳ :
  ⦃ props : Has (1# is rightIdentity for * ∷ 0# is rightZero for * ∷ []) ⦄ →
  ∀ {n} (i : Fin n) t j → (lookup t j *′ 1● j i) ≈′ lookup (Table.select 0′ i t) j
1-selectʳ i t j with i Fin.≟ j | j Fin.≟ i
1-selectʳ ⦃ props ⦄ i t .i | yes ≡.refl | yes q = from props (1# is rightIdentity for *) _
1-selectʳ .j t j | yes ≡.refl | no ¬q = ⊥-elim (¬q ≡.refl)
1-selectʳ i t .i | no ¬p | yes ≡.refl = ⊥-elim (¬p ≡.refl)
1-selectʳ ⦃ props ⦄ i t j | no _ | no ¬p = from props (0# is rightZero for *) _

1-sym : ∀ {n} (i j : Fin n) → 1● i j ≈′ 1● j i
1-sym i j with i Fin.≟ j | j Fin.≟ i
1-sym i j | yes _ | yes _ = S.refl
1-sym i j | no _  | no _ = S.refl
1-sym i .i | yes ≡.refl | no ¬q = ⊥-elim (¬q ≡.refl)
1-sym i .i | no ¬p | yes ≡.refl = ⊥-elim (¬p ≡.refl)

⊗-identityˡ :
  ⦃ props : Has ( 1# is leftIdentity for *
                ∷ 0# is leftZero for *
                ∷ 0# is leftIdentity for +
                ∷ 0# is rightIdentity for +
                ∷ associative on +
                ∷ commutative on +
                ∷ []) ⦄ →
  ∀ {m n} → ∀ (A : Matrix S m n) → (1● ⊗ A) ≈ A
⊗-identityˡ ⦃ props ⦄ {m} A i k =
  begin
    ∑[ j < m ] (1● i j *′ A j k)                        ≈⟨ sumₜ-cong (1-selectˡ ⦃ weaken props ⦄ i _) ⟩
    sumₜ (Table.select 0′ i (tabulate (λ x → A x k)))   ≈⟨ select-sum ⦃ weaken props ⦄ {m} _ ⟩
    A i k                                               ∎
  where open EqReasoning S.setoid

⊗-identityʳ :
  ⦃ props : Has ( 1# is rightIdentity for *
                ∷ 0# is rightZero for *
                ∷ 0# is leftIdentity for +
                ∷ 0# is rightIdentity for +
                ∷ associative on +
                ∷ commutative on +
                ∷ []) ⦄ →
  ∀ {m n} → ∀ (A : Matrix S m n) → (A ⊗ 1●) ≈ A
⊗-identityʳ ⦃ props ⦄ {n = n} A i k =
  begin
    ∑[ j < n ] (A i j *′ 1● j k)                ≈⟨ sumₜ-cong (1-selectʳ ⦃ weaken props ⦄ k _) ⟩
    sumₜ (Table.select 0′ k (tabulate (A i)))   ≈⟨ select-sum ⦃ weaken props ⦄ {n} _ ⟩
    A i k                                       ∎
  where open EqReasoning S.setoid

⊗-distributesOverˡ-⊕ :
  ⦃ props : Has (* ⟨ distributesOverˡ ⟩ₚ + ∷ 0# is leftIdentity for + ∷ associative on + ∷ commutative on + ∷ []) ⦄ →
  ∀ {m n o} (M : Matrix S m n) (A B : Matrix S n o) →
  M ⊗ (A ⊕ B) ≈ (M ⊗ A) ⊕ (M ⊗ B)
⊗-distributesOverˡ-⊕ ⦃ props ⦄ {n = n} M A B i k =
  begin
    ∑[ j < n ] (M i j *′ (A j k +′ B j k))                      ≈⟨ sumₜ-cong (λ j → from props (* ⟨ distributesOverˡ ⟩ₚ +) (M i j) (A j k) (B j k)) ⟩
    ∑[ j < n ] (M i j *′ A j k +′ M i j *′ B j k)               ≈⟨ S.sym (∑-+′-hom ⦃ weaken props ⦄ n (λ j → M i j *′ A j k) (λ j → M i j *′ B j k)) ⟩
    ∑[ j < n ] (M i j *′ A j k) +′ ∑[ j < n ] (M i j *′ B j k)  ∎
  where open EqReasoning S.setoid
