module MLib.Algebra.PropertyCode where

open import MLib.Prelude
open import MLib.Prelude.Fin.Pieces
open import MLib.Prelude.FiniteInj
open import MLib.Algebra.PropertyCode.RawStruct
open import MLib.Algebra.PropertyCode.Core
open import MLib.Algebra.Instances

open import Relation.Binary as B using (Setoid)

open List using (_∷_; [])
open import Data.List.All as All using (All; _∷_; []) public
open import Data.List.Any using (Any; here; there)
open import Data.List.Any.Membership.Propositional using (_∈_)

open import Data.Vec using (Vec; _∷_; [])
open import Data.Vec.N-ary
open import Data.Vec.Relation.InductivePointwise using (Pointwise; []; _∷_)

open import Data.Product.Relation.SigmaPropositional as OverΣ using (OverΣ)

open import Data.Bool using (T)

open import Category.Applicative

open import Function.Inverse using (_↔_)
open import Function.LeftInverse using (_↞_; LeftInverse)
open import Function.Equality using (_⟨$⟩_)

-- import Data.Table as Table hiding (module Table)
open Table using (Table)

--------------------------------------------------------------------------------
--  Some named property combinations
--------------------------------------------------------------------------------

private
  Maybe-applicative : ∀ {ℓ} → RawApplicative {ℓ} Maybe
  Maybe-applicative = record
    { pure = just
    ; _⊛_ = maybe Maybe.map λ _ → nothing
    }

subΠ : ∀ {k k′} {code : Code k} {code′ : Code k′} →
  let open Code code using (K)
      open Code code′ using () renaming (K to K′)
  in (∀ {n} → K′ n → Maybe (K n)) →
     Properties code → Properties code′ → Properties code′
hasProperty (subΠ f Π₀ Π₁) π = {!!}

data MagmaK : ℕ → Set where
  ∙ : MagmaK 2

data MonoidK : ℕ → Set where
  ε : MonoidK 0
  ∙ : MonoidK 2

data BimonoidK : ℕ → Set where
  0# 1# : BimonoidK 0
  + * : BimonoidK 2

module _ where
  open Code
  open ℕ

  magmaCode : Code _
  K magmaCode = MagmaK
  boundAt magmaCode 2 = 1
  boundAt magmaCode _ = 0
  isFiniteAt magmaCode 0 = empty-isFinite λ ()
  isFiniteAt magmaCode 1 = empty-isFinite λ ()
  isFiniteAt magmaCode (suc (suc (suc _))) = empty-isFinite λ ()
  isFiniteAt magmaCode 2 = unitary-isFinite (≡.setoid _) ∙ λ {∙ → ≡.refl}

  monoidCode : Code _
  K monoidCode = MonoidK
  boundAt monoidCode 0 = 1
  boundAt monoidCode 2 = 1
  boundAt monoidCode _ = 0
  isFiniteAt monoidCode 0 = unitary-isFinite (≡.setoid _) ε λ {ε → ≡.refl}
  isFiniteAt monoidCode 1 = empty-isFinite λ ()
  isFiniteAt monoidCode 2 = unitary-isFinite (≡.setoid _) ∙ λ {∙ → ≡.refl}
  isFiniteAt monoidCode (suc (suc (suc _))) = empty-isFinite λ ()

--   bimonoidCode : Code _
--   K bimonoidCode = BimonoidK
--   allAtArity bimonoidCode zero = 0# ∷ 1# ∷ []
--   allAtArity bimonoidCode (suc (suc zero)) = + ∷ * ∷ []
--   allAtArity bimonoidCode _ = []

+-part : ∀ {n} → BimonoidK n → Maybe (MonoidK n)
+-part 0# = just ε
+-part + = just ∙
+-part _ = nothing

*-part : ∀ {n} → BimonoidK n → Maybe (MonoidK n)
*-part 1# = just ε
*-part * = just ∙
*-part _ = nothing

isSemigroup : Properties magmaCode
isSemigroup = properties
  λ { (associative , ∙ ∷ []) → true
    ; _ → false}

-- isMonoid : Properties monoidCode
-- isMonoid = subΠ (λ {∙ → just ∙; _ → nothing}) isSemigroup (properties
--   λ { (leftIdentity ε ∙) → true
--     ; (rightIdentity ε ∙) → true
--     ; _ → false
--     })

-- isCommutativeMonoid : Properties monoidCode
-- isCommutativeMonoid = subΠ just isMonoid (properties
--   λ { (commutative ∙) → true
--     ; _ → false
--     })

-- isSemiring : Properties bimonoidCode
-- isSemiring =
--   subΠ +-part isCommutativeMonoid (
--   subΠ *-part isMonoid (properties
--   λ { (leftZero 0# *) → true
--     ; (rightZero 0# *) → true
--     ; (* distributesOverˡ +) → true
--     ; (* distributesOverʳ +) → true
--     ; _ → false
--     }))

-- module Into where
--   open Algebra using (Semigroup; Monoid; CommutativeMonoid)

--   semigroup : ∀ {c ℓ} {Π : Properties magmaCode} ⦃ hasSemigroup : HasAll (Π ⇒ₚ isSemigroup) ⦄ → Struct c ℓ Π → Semigroup c ℓ
--   semigroup struct = record
--     { _∙_ = ⟦ ∙ ⟧
--     ; isSemigroup = record
--       { isEquivalence = isEquivalence
--       ; assoc = {!use (associative ∙)!}
--       ; ∙-cong = {!!}
--       }
--     }
--     where open Struct struct

-- -- -- --   monoid : ∀ {c ℓ} {props} ⦃ _ : isMonoid ⊆ props ⦄ → Dagma props c ℓ → Monoid c ℓ
-- -- -- --   monoid ⦃ mon ⦄ dagma = record
-- -- -- --     { isMonoid = record
-- -- -- --       { isSemigroup = S.isSemigroup
-- -- -- --       ; identity = proj₂ (from isMonoid hasIdentity)
-- -- -- --       }
-- -- -- --     }
-- -- -- --     where
-- -- -- --       open Dagma dagma
-- -- -- --       module S = Semigroup (semigroup (dagma ↓M isMonoid ↓M isSemigroup))

-- -- -- --   commutativeMonoid : ∀ {c ℓ} {props} ⦃ _ : isCommutativeMonoid ⊆ props ⦄ → Dagma props c ℓ → CommutativeMonoid c ℓ
-- -- -- --   commutativeMonoid dagma = record
-- -- -- --     { isCommutativeMonoid = record
-- -- -- --       { isSemigroup = S.isSemigroup
-- -- -- --       ; leftIdentity = proj₁ (proj₂ (from isCommutativeMonoid hasIdentity))
-- -- -- --       ; comm = from isCommutativeMonoid commutative
-- -- -- --       }
-- -- -- --     }
-- -- -- --     where
-- -- -- --       open Dagma dagma
-- -- -- --       module S = Semigroup (semigroup (dagma ↓M isCommutativeMonoid ↓M isSemigroup))

-- -- -- --   -- semiring
