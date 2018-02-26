module MLib.Matrix where

open import MLib.Prelude
open import MLib.Algebra.PropertyCode
open import MLib.Algebra.PropertyCode.Structures

open import Data.Vec.Relation.InductivePointwise using (Pointwise; []; _∷_)

open Algebra using (CommutativeMonoid)

open PropertyC

module _ {ℓ} where

  Matrix : Set ℓ → ℕ → ℕ → Set ℓ
  Matrix S m n = Fin m → Fin n → S

module _ {c ℓ} (struct : Struct bimonoidCode c ℓ) where
  module S = Struct struct renaming (Carrier to S; _≈_ to _≈′_)
  open S using (S; _≈′_; _⟨_⟩_; ⟦_⟧; from; from′; use; Has; HasList; HasEach)

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

    open Algebra.FunctionProperties _≈_

    -- Pointwise addition --

    _⊕_ : Matrix S m n → Matrix S m n → Matrix S m n
    (A ⊕ B) i j = A i j ⟨ + ⟩ B i j

    ⊕-cong : Congruent₂ _⊕_
    ⊕-cong p q = λ i j → S.congⁿ + (p i j ∷ q i j ∷ [])

    assoc : ⦃ _ : HasList (associative on + ∷ []) ⦄ → Associative _⊕_
    assoc A B C i j = from′ (associative on + ∷ []) (associative on +) (A i j) (B i j) (C i j)

    0● : Matrix S m n
    0● _ _ = ⟦ 0# ⟧

    identityˡ : ⦃ _ : Has (0# is leftIdentity for +) ⦄ → LeftIdentity 0● _⊕_
    identityˡ A i j = use (0# is leftIdentity for +) (A i j)

    identityʳ : ⦃ _ : Has (0# is rightIdentity for +) ⦄ → RightIdentity 0● _⊕_
    identityʳ A i j = use (0# is rightIdentity for +) (A i j)


    -- module _ ⦃ _ : HasEach isCommutativeMonoid ⦄ where
--       +-commutativeMonoid : CommutativeMonoid ℓ p
--       +-commutativeMonoid = Into.commutativeMonoid +-dagma

--       private
--         module M where
--           open import Algebra.Operations.CommutativeMonoid +-commutativeMonoid public
--           open import Algebra.Properties.CommutativeMonoid +-commutativeMonoid public
--       open M using (sumTable; sumTable-syntax)

      -- sumDistribˡ : ∀ {n} c f → c ⊛ sum n f ≈′ ∑[ i < n ] (c ⊛ f i)
      -- sumDistribˡ {Nat.zero} _ _ = proj₂ S.zero _
      -- sumDistribˡ {Nat.suc n} c f =
      --   begin
      --     c ⊛ (f _ ⊕ sum n (f ∘ Fin.suc))                 ≈⟨ proj₁ S.distrib _ _ _ ⟩
      --     c ⊛ f _ ⊕ c ⊛ sum _ (f ∘ Fin.suc)               ≈⟨ S.+-cong S.refl (sumDistribˡ c (f ∘ Fin.suc)) ⟩
      --     c ⊛ f _ ⊕ sum _ (λ x → c ⊛ (f ∘ Fin.suc) x)     ∎
      --   where open EqReasoning S.setoid

  --   sumDistribʳ : ∀ {n} c f → sum n f ⊛ c ≈′ ∑[ i < n ] (f i ⊛ c)
  --   sumDistribʳ {Nat.zero} _ _ = proj₁ S.zero _
  --   sumDistribʳ {Nat.suc n} c f =
  --     begin
  --       (f _ ⊕ sum n (f ∘ Fin.suc)) ⊛ c                 ≈⟨ proj₂ S.distrib _ _ _ ⟩
  --       f _ ⊛ c ⊕ sum n (f ∘ Fin.suc) ⊛ c               ≈⟨ S.+-cong S.refl (sumDistribʳ c (f ∘ Fin.suc)) ⟩
  --       f _ ⊛ c ⊕ sum n (λ x → (f ∘ Fin.suc) x ⊛ c)     ∎
  --     where open EqReasoning S.setoid

  --   module _ {n : ℕ} where
  --     open Setoids S.setoid {n} {n}
  --     open Algebra.FunctionProperties _≈_

  --     _*_ : Matrix S n n → Matrix S n n → Matrix S n n
  --     (A * B) i k = ∑[ j < _ ] (A i j ⊛ B j k)

  --     1# : Matrix S n n
  --     1# i j with i Fin+.≟ j
  --     1# i j | yes _ = S.1#
  --     1# i j | no  _ = S.0#

  --     module +-CommutativeMonoid where
  --       comm : Commutative _+_
  --       comm A B i j = S.+-comm (A i j) (B i j)

  --       open +-Monoid {n} public

  --     +-commutativeMonoid : IsCommutativeMonoid _≈_ _+_ 0#
  --     +-commutativeMonoid = record { isSemigroup = record { Setoids S.setoid; +-CommutativeMonoid } ; +-CommutativeMonoid }

  --     module *-Monoid where
  --       ∙-cong : Congruent₂ _*_
  --       ∙-cong {x = A₁} {y = A₂} {u = B₁} {v = B₂} p q i k = M.sum-cong (λ j → S.*-cong (p i j) (q j k))

  --       assoc : Associative _*_
  --       assoc A B C i l =
  --         begin
  --           ((A * B) * C) i l                                  ≡⟨⟩
  --           ∑[ k < n ] (∑[ j < n ] (A i j ⊛ B j k) ⊛ C k l)    ≈⟨ M.sum-cong (λ k → sumDistribʳ (C k l) (λ j → A i j ⊛ B j k)  ) ⟩
  --           ∑[ k < n ] (∑[ j < n ] (A i j ⊛ B j k ⊛ C k l))    ≈⟨ M.sum-cong (λ k → M.sum-cong (λ j → S.*-assoc (A i j) (B j k) (C k l))) ⟩
  --           ∑[ k < n ] (∑[ j < n ] (A i j ⊛ (B j k ⊛ C k l)))  ≈⟨ M.sum-comm n n _ ⟩
  --           ∑[ j < n ] (∑[ k < n ] (A i j ⊛ (B j k ⊛ C k l)))  ≈⟨ M.sum-cong (λ j → S.sym (sumDistribˡ (A i j) (λ k → B j k ⊛ C k l))) ⟩
  --           ∑[ j < n ] (A i j ⊛ ∑[ k < n ] (B j k ⊛ C k l))    ≡⟨⟩
  --           (A * (B * C)) i l                                    ∎
  --         where open EqReasoning S.setoid

  --       1-*-comm : ∀ i j x → 1# i j ⊛ x ≈′ x ⊛ 1# i j
  --       1-*-comm i j x with i Fin+.≟ j
  --       1-*-comm i j x | yes p = S.trans (proj₁ S.*-identity x) (S.sym (proj₂ S.*-identity x))
  --       1-*-comm i j x | no ¬p = S.trans (proj₁ S.zero x) (S.sym (proj₂ S.zero x))

  --       1-select : ∀ i f j → (1# i j ⊛ f j) ≈′ M.select i f j
  --       1-select i f j with i Fin+.≟ j | j Fin+.≟ i
  --       1-select i f .i | yes ≡.refl | yes q = proj₁ S.*-identity _
  --       1-select .j f j | yes ≡.refl | no ¬q = ⊥-elim (¬q ≡.refl)
  --       1-select i f .i | no ¬p | yes ≡.refl = ⊥-elim (¬p ≡.refl)
  --       1-select i f j | no _ | no ¬p = proj₁ S.zero _

  --       1-sym : ∀ i j → 1# i j ≈′ 1# j i
  --       1-sym i j with i Fin+.≟ j | j Fin+.≟ i
  --       1-sym i j | yes _ | yes _ = S.refl
  --       1-sym i j | no _  | no _ = S.refl
  --       1-sym i .i | yes ≡.refl | no ¬q = ⊥-elim (¬q ≡.refl)
  --       1-sym i .i | no ¬p | yes ≡.refl = ⊥-elim (¬p ≡.refl)

  --       identityˡ : LeftIdentity 1# _*_
  --       identityˡ A i k =
  --         begin
  --           ∑[ j < n ] (1# i j ⊛ A j k)               ≈⟨ M.sum-cong (1-select i _) ⟩
  --           ∑[ j < n ] (M.select i (λ x → A x k) j)   ≈⟨ M.select-sum (λ i → A i k) ⟩
  --           A i k                                     ∎
  --         where open EqReasoning S.setoid

  --       identityʳ : RightIdentity 1# _*_
  --       identityʳ A i k =
  --         begin
  --           ∑[ j < n ] (A i j ⊛ 1# j k)     ≈⟨ M.sum-cong (λ j → S.*-cong S.refl (1-sym j k)) ⟩
  --           ∑[ j < n ] (A i j ⊛ 1# k j)     ≈⟨ M.sum-cong (λ j → S.sym (1-*-comm k j (A i j))) ⟩
  --           ∑[ j < n ] (1# k j ⊛ A i j)     ≈⟨ M.sum-cong (1-select k (A i)) ⟩
  --           ∑[ j < n ] M.select k (A i) j   ≈⟨ M.select-sum (A i) ⟩
  --           A i k                           ∎
  --         where open EqReasoning S.setoid

  --       identity : Identity 1# _*_
  --       identity = identityˡ , identityʳ

  --     *-monoid : IsMonoid _≈_ _*_ 1#
  --     *-monoid = record { isSemigroup = record { Setoids S.setoid; *-Monoid }; *-Monoid }

  --   -- module _ {m n : ℕ} where
  --   --   _⊗_ : Matrix S m → Matrix S n → Matrix S (m Nat.* n)
  --   --   (A ⊗ B) i j = {!!}
