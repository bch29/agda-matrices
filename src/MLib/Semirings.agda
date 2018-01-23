module MLib.Semirings where

open import MLib.Prelude
open Algebra using (Semiring)

module _ {ℓ p} (semiring : Semiring ℓ p) where
  open Semiring semiring renaming (Carrier to S)

  pow : ℕ → S → S
  pow Nat.zero x = 1#
  pow (Nat.suc n) x = x * pow n x

  powsum : ℕ → S → S
  powsum Nat.zero x = 1#
  powsum (Nat.suc n) x = pow (Nat.suc n) x + powsum n x

  Q-stable : ℕ → S → Set p
  Q-stable q x = powsum (1 Nat.+ q) x ≈ powsum q x
