open import MLib.Algebra.PropertyCode
open import MLib.Algebra.PropertyCode.Structures

module MLib.Matrix.SemiTensor.Core {c ℓ} (struct : Struct bimonoidCode c ℓ) where

open import MLib.Prelude
open import MLib.Matrix.Core
open import MLib.Matrix.Equality struct
open import MLib.Matrix.Mul struct
open import MLib.Matrix.Tensor struct
open import MLib.Algebra.Operations struct

open Nat using () renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)

open import MLib.Fin.Parts.Simple

open import Data.Nat.LCM
open import Data.Nat.Divisibility

chunkVec : ∀ {m n} → Table S (m *ℕ n) → Table (Table S n) m
chunkVec {m} {n} t .lookup i .lookup j = lookup t (intoPart (i , j))

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

_⋉_ : ∀ {m n p q} → Matrix S m n → Matrix S p q → Matrix S _ _
_⋉_ {m} {n} {p} {q} = Defn.stp {n} {p} (lcm n p .proj₂)

