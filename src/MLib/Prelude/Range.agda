--------------------------------------------------------------------------------
--  Numbers in a particular (inclusive) range of naturals
--------------------------------------------------------------------------------

module MLib.Prelude.Range where

open import MLib.Prelude.FromStdlib

import MLib.Prelude.Fin as Fin
open Fin using (Fin)

import MLib.Prelude.AtLeast as AtLeast
open AtLeast using (AtLeast)

import Function.Inverse as Inv

infix 9 Range

data Range (a : ℕ) : AtLeast a → Set where
  rngBot : ∀ {b} → Range a b
  rngSuc : ∀ {b} → Range a b → Range a (AtLeast.α-suc b)

syntax Range a b = [ a ⋯ b ]

RangePlus : (a b : ℕ) → Set
RangePlus a b = Range a (AtLeast.a+ b)

module _ {a} where
  toFin : ∀ {b} → [ a ⋯ b ] → Fin (Nat.suc (AtLeast.toℕ b))
  toFin {b} rngBot = Fin.inject≤ (Fin.fromℕ a) (Nat.s≤s (AtLeast.a≤α b))
  toFin (rngSuc r) = Fin.suc (toFin r)

  toℕ : ∀ {b} → [ a ⋯ b ] → ℕ
  toℕ rngBot = a
  toℕ (rngSuc r) = Nat.suc (toℕ r)

  toFin-correct : ∀ {b} (r : [ a ⋯ b ]) → Fin.toℕ (toFin r) ≡ toℕ r
  toFin-correct {b} rngBot =
    begin
      Fin.toℕ (Fin.inject≤ (Fin.fromℕ a) (Nat.s≤s (AtLeast.a≤α b)))  ≡⟨ Fin.inject≤-lemma _ _ ⟩
      Fin.toℕ (Fin.fromℕ a)                                          ≡⟨ Fin.to-from a ⟩
      a                                                               ∎
    where open ≡.≡-Reasoning
  toFin-correct (rngSuc r) = ≡.cong Nat.suc (toFin-correct r)

  ∸a : ∀ {b} → Range a b → Fin (Nat.suc (AtLeast.∸a b))
  ∸a rngBot = Fin.zero
  ∸a (rngSuc r) = Fin.suc (∸a r)

  a+′ : ∀ {b} → Fin (Nat.suc b) → Range a (AtLeast.a+ b)
  a+′ Fin.zero = rngBot
  a+′ {ℕ.zero} (Fin.suc ())
  a+′ {ℕ.suc b} (Fin.suc i) = rngSuc (a+′ i)

  a+ : ∀ {b} → Fin (Nat.suc (AtLeast.∸a b)) → Range a b
  a+ Fin.zero = rngBot
  a+ {AtLeast.α-eq} (Fin.suc ())
  a+ {AtLeast.α-suc b} (Fin.suc i) = rngSuc (a+ i)

  ∸a-a+ : ∀ {b} (α : Fin (Nat.suc (AtLeast.∸a b))) → ∸a (a+ α) ≡ α
  ∸a-a+ Fin.zero = ≡.refl
  ∸a-a+ {AtLeast.α-eq} (Fin.suc ())
  ∸a-a+ {AtLeast.α-suc b} (Fin.suc α) = ≡.cong Fin.suc (∸a-a+ α)

  a+-∸a : ∀ {b} (r : Range a b) → a+ (∸a r) ≡ r
  a+-∸a rngBot = ≡.refl
  a+-∸a (rngSuc r) = ≡.cong rngSuc (a+-∸a r)

  rngTop : ∀ {b} → Range a b
  rngTop {AtLeast.α-eq} = rngBot
  rngTop {AtLeast.α-suc _} = rngSuc rngTop

  open Inv

  ∸a-inverse : ∀ {b} → Range a b ↔ Fin (Nat.suc (AtLeast.∸a b))
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

  ∸a-inverse′ : ∀ {b} → Range a (AtLeast.a+ b) ↔ Fin (Nat.suc b)
  ∸a-inverse′ {b} =
    ≡.subst₂
    (λ b₁ b₂ → Range a b₁ ↔ Fin (Nat.suc b₂))
    ≡.refl (AtLeast.∸a-a+ b)
    (∸a-inverse {AtLeast.a+ b})
