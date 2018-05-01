open import MLib.Algebra.PropertyCode
open import MLib.Algebra.PropertyCode.Structures

module MLib.Matrix.SemiTensor.Associativity {c ℓ} (struct : Struct bimonoidCode c ℓ) where

open import MLib.Prelude
open import MLib.Matrix.Core
open OverBimonoid struct
open import MLib.Matrix.Mul struct
open import MLib.Matrix.Tensor struct
open import MLib.Matrix.SemiTensor.Core struct
open import MLib.Algebra.Operations struct

open Nat using () renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)

open import MLib.Fin.Pieces.Simple

open import Data.Nat.LCM
open import Data.Nat.Divisibility

module _ ⦃ props : Has (1# is rightIdentity for * ∷ associative on * ∷ []) ⦄ where
  open _≃_

  {-
  m *ℕ (lcm n (p * (lcm q r) / q))/n ≡ m *ℕ (lcm n p)/n *ℕ (lcm (q *ℕ (lcm n p)/p) r) / r

  m * lcm(n, p * lcm(q, r) / q) / n =
  m * (lcm(n, p) / n) * lcm (q * lcm(n, p) / p,  r) / r

  lcm(n, p * lcm(q, r) / q) = lcm (q * lcm(n, p) / p,  r) * p / q

  f(a, b) = lcm(a, b) / a

  lcm(n, p * f(q, r)) = lcm(r, q * f(p, n)) * p / q
  -}

  module _ {m n p q r s} (A : Matrix S m n) (B : Matrix S p q) (C : Matrix S r s) where
    t₁ = lcm n p .proj₁
    lcm-n-p=t₁ = lcm n p .proj₂

    open Defn lcm-n-p=t₁ using () renaming (t/n to t₁/n; t/p to t₁/p)

    t₂ = lcm q r .proj₁
    lcm-q-r=t₂ = lcm q r .proj₂

    open Defn lcm-q-r=t₂ using () renaming (t/n to t₂/q; t/p to t₂/r)

    t₃ = lcm n (p *ℕ t₂/q) .proj₁
    lcm-n-pt₂/q=t₃ = lcm n (p *ℕ t₂/q) .proj₂

    open Defn lcm-n-pt₂/q=t₃ using () renaming (t/n to t₃/n; t/p to t₃/[p*t₂/q])

    t₄ = lcm (q *ℕ t₁/p) r .proj₁
    lcm-qt₁/p-r=t₄ = lcm (q *ℕ t₁/p) r .proj₂

    open Defn lcm-qt₁/p-r=t₄ using () renaming (t/n to t₄/[q*t₁/p]; t/p to t₄/r)
    -- module D₁ = Defn {n} {p} {q}
    -- module D₂ = Defn {q} {r} {s}

    ⋉-associative : A ⋉ (B ⋉ C) ≃ (A ⋉ B) ⋉ C
    ⋉-associative .m≡p = {!!}
    ⋉-associative .n≡q = {!!}
    ⋉-associative .equal = {!!}
