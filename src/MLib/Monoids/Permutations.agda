open import MLib.Prelude

open Algebra using (CommutativeMonoid)

module MLib.Monoids.Permutations {c ℓ} (commutativeMonoid : CommutativeMonoid c ℓ) where

open CommutativeMonoid commutativeMonoid public
  renaming (Carrier to S; ε to 0#; _∙_ to _+_; ∙-cong to +-cong)

open import Algebra.Properties.CommutativeMonoid commutativeMonoid public
open import Algebra.Operations.CommutativeMonoid commutativeMonoid public

open EqReasoning setoid

open import Function.Equality using (_⟨$⟩_)
open import Function.Inverse using (Inverse; _↔_)
open import Data.Fin using (punchIn)
open import Data.Fin.Vec using (select)
open import Data.Fin.Properties




