open import MLib.Algebra.PropertyCode
open import MLib.Algebra.PropertyCode.Structures

module MLib.Matrix.Pow {c ℓ} (struct : Struct bimonoidCode c ℓ) where

open import MLib.Prelude
open import MLib.Matrix.Core
open import MLib.Matrix.Equality struct
open import MLib.Matrix.Mul struct
open import MLib.Matrix.Plus struct
open import MLib.Matrix.Bimonoid struct

open FunctionProperties

module _ {n} where
  open import MLib.Algebra.Operations (matrixStruct n)

  pow : Matrix S n n → ℕ → Matrix S n n
  pow M zero = 1●
  pow M (suc p) = M ⊗ pow M p

  pstar : Matrix S n n → ℕ → Matrix S n n
  pstar M zero = 0●
  pstar M (suc p) = 1● ⊕ M ⊗ pstar M p

  pstar′ : Matrix S n n → ℕ → Matrix S n n
  pstar′ M p = ∑[ q < p ] pow M (Fin.toℕ q)

  pstar′-unfold : ∀ {M : Matrix S n n} {p} → pstar′ M (suc p) ≈ 1● ⊕ M ⊗ pstar′ M p
  pstar′-unfold {M} {p} =
    begin
      pstar′ M (suc p)                                                  ≡⟨⟩
      pow M (Fin.toℕ (zero {p})) ⊕ ∑[ q < p ] pow M (Fin.toℕ (suc q))  ≡⟨⟩
      1● ⊕ ∑[ q < p ] pow M (suc (Fin.toℕ q))                          ≡⟨⟩
      1● ⊕ ∑[ q < p ] (M ⊗ pow M (Fin.toℕ q))                          ≈⟨ ⊕-cong refl (sym (sumDistribˡ ⦃ {!!} ⦄ {p} M _)) ⟩
      1● ⊕ M ⊗ ∑[ q < p ] pow M (Fin.toℕ q)                            ≡⟨⟩
      1● ⊕ M ⊗ pstar′ M p                                               ∎
    where open EqReasoning setoid

  -- pstar-pstar′ : ∀ {M : Matrix S n n} {p} → pstar M p ≈ pstar′ M p
  -- pstar-pstar′ {p = zero} _ _ = S.refl
  -- pstar-pstar′ {M = M} {suc p} =
  --   begin
  --     ((1● ⊕ M) ⊗ pstar M p)  ≈⟨ {!!} ⟩
  --     pow M (Fin.toℕ (zero {p})) ⊕ (Table.foldr {n = p} _⊕_ 0● (tabulate (pow M ∘ Fin.toℕ ∘ suc))) ≡⟨⟩
  --     pstar′ M (suc p)        ∎
  --   where open EqReasoning setoid
