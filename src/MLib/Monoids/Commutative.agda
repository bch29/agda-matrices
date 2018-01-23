open import MLib.Prelude

open Algebra using (CommutativeMonoid)

module MLib.Monoids.Commutative {c ℓ} (commutativeMonoid : CommutativeMonoid c ℓ) where

open CommutativeMonoid commutativeMonoid public
  renaming (Carrier to S; ε to 0#; _∙_ to _+_; ∙-cong to +-cong)

open import Algebra.Properties.CommutativeMonoid commutativeMonoid public
open import Algebra.Operations.CommutativeMonoid commutativeMonoid public

open import MLib.Prelude.Paths

import Relation.Binary.Sigma.Pointwise as Σ

open EqReasoning setoid

--------------------------------------------------------------------------------
--  Theorems
--------------------------------------------------------------------------------

-- Heterogeneous sumFin congruence
sumFin-cong′ : ∀ {m n} {f g} → OverΣ (λ f′ g′ → ∀ i → f′ i ≈ g′ i) (m , f) (n , g) → sumFin m f ≈ sumFin n g
sumFin-cong′ (≡.refl , q) = sumFin-cong q

-- Heterogeneous propositional sumFin congruence
sumFin-cong≡′ : ∀ {m n f g} → OverΣ _≗_ (m , f) (n , g) → sumFin m f ≡ sumFin n g
sumFin-cong≡′ (≡.refl , q) = sumFin-cong≡ q
