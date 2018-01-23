--------------------------------------------------------------------------------
--  Numbers which are at least a particular natural
--------------------------------------------------------------------------------

module MLib.Prelude.AtLeast where

open import MLib.Prelude.FromStdlib
import MLib.Prelude.Fin as Fin
open Fin using (Fin)

import Function.Inverse as Inv

data AtLeast (a : ℕ) : Set where
  α-eq : AtLeast a
  α-suc : AtLeast a → AtLeast a

module _ {a : ℕ} where
  toℕ : AtLeast a → ℕ
  toℕ α-eq = a
  toℕ (α-suc α) = Nat.suc (toℕ α)

  a≤α : (α : AtLeast a) → a Nat.≤ toℕ α
  a≤α α-eq = Nat.≤-refl
  a≤α (α-suc α) = Nat.≤-step (a≤α α)

  ∸a : AtLeast a → ℕ
  ∸a α-eq = 0
  ∸a (α-suc α) = Nat.suc (∸a α)

  ∸a-correct : ∀ α → ∸a α ≡ toℕ α Nat.∸ a
  ∸a-correct α-eq = ≡.sym (Nat.m+n∸n≡m 0 a)
  ∸a-correct (α-suc α) =
    begin
      suc (∸a α)          ≡⟨ ≡.cong suc (∸a-correct α) ⟩
      suc (toℕ α ∸ a)     ≡⟨ ≡.sym (+-∸-assoc 1 (a≤α α)) ⟩
      suc (toℕ α) ∸ a     ∎
    where open ≡.≡-Reasoning
          open Nat

  a+ : ℕ → AtLeast a
  a+ ℕ.zero = α-eq
  a+ (ℕ.suc b) = α-suc (a+ b)

  a+-correct : ∀ b → toℕ (a+ b) ≡ a Nat.+ b
  a+-correct ℕ.zero = ≡.sym (Nat.+-identityʳ _)
  a+-correct (ℕ.suc b) =
    begin
      suc (toℕ (a+ b))  ≡⟨ ≡.cong suc (a+-correct b) ⟩
      suc (a + b)       ≡⟨ ≡.sym (+-suc a b) ⟩
      a + suc b         ∎
    where open ≡.≡-Reasoning
          open Nat

  open Inv

  ∸a-a+ : ∀ n → ∸a (a+ n) ≡ n
  ∸a-a+ ℕ.zero = ≡.refl
  ∸a-a+ (ℕ.suc n) = ≡.cong Nat.suc (∸a-a+ n)

  a+-∸a : ∀ α → a+ (∸a α) ≡ α
  a+-∸a α-eq = ≡.refl
  a+-∸a (α-suc α) = ≡.cong α-suc (a+-∸a α)

  ∸a-inverse : AtLeast a ↔ ℕ
  ∸a-inverse = record
    { to = record
      { _⟨$⟩_ = ∸a
      ; cong = ≡.cong ∸a
      }
    ; from = record
      { _⟨$⟩_ = a+
      ; cong = ≡.cong a+
      }
    ; inverse-of = record
      { left-inverse-of = a+-∸a
      ; right-inverse-of = ∸a-a+
      }
    }
