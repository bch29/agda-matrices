module MLib.Algebra.PropertyCode.Structures where

open import MLib.Prelude
open import MLib.Finite

open import MLib.Algebra.PropertyCode.RawStruct public
open import MLib.Algebra.PropertyCode.Core public
open import MLib.Algebra.PropertyCode public

open import Relation.Binary as B using (Setoid)

open import Data.List.Any using (Any; here; there)
open import Data.Bool using (_∨_)

open import Category.Applicative

--------------------------------------------------------------------------------
--  Combinators for constructing property sets from smaller sets
--------------------------------------------------------------------------------

subΠ : ∀ {k k′} {code : Code k} {code′ : Code k′} →
  let open Code code using (K)
      open Code code′ using () renaming (K to K′)
  in (∀ {n} → K′ n → Maybe (K n)) →
     Properties code → Properties code′ → Properties code′
hasProperty (subΠ f Π₀ Π₁) (π , κs) = hasProperty Π₁ (π , κs) ∨ satUnder
  where
    satUnder : Bool
    satUnder with List.All.traverse f κs
    satUnder | just κs′ = hasProperty Π₀ (π , κs′)
    satUnder | nothing = false

subΠ′ : ∀ {k k′} {code : Code k} {code′ : Code k′} →
  let open Code code using (K)
      open Code code′ using () renaming (K to K′)
  in (∀ {n} → K′ n → Maybe (K n)) →
     Properties code → List (Property K′) → Properties code′
subΠ′ f Π πs = subΠ f Π (fromList πs)

--------------------------------------------------------------------------------
--  Code Types
--------------------------------------------------------------------------------

data MagmaK : ℕ → Set where
  ∙ : MagmaK 2

data MonoidK : ℕ → Set where
  ε : MonoidK 0
  ∙ : MonoidK 2

data BimonoidK : ℕ → Set where
  0# 1# : BimonoidK 0
  + * : BimonoidK 2

--------------------------------------------------------------------------------
--  Code Proofs
--------------------------------------------------------------------------------

module _ where
  open Code

  -- TODO: automate proofs like these.

  magmaCode : Code _
  K magmaCode = MagmaK
  boundAt magmaCode 2 = 1
  boundAt magmaCode _ = 0
  isFiniteAt magmaCode 0 = enumerable-isFiniteSet [] λ ()
  isFiniteAt magmaCode 1 = enumerable-isFiniteSet [] λ ()
  isFiniteAt magmaCode (suc (suc (suc _))) = enumerable-isFiniteSet [] λ ()
  isFiniteAt magmaCode 2 = enumerable-isFiniteSet (∙ ∷ []) λ {∙ → here ≡.refl}

  monoidCode : Code _
  K monoidCode = MonoidK
  boundAt monoidCode 0 = 1
  boundAt monoidCode 2 = 1
  boundAt monoidCode _ = 0
  isFiniteAt monoidCode 0 = enumerable-isFiniteSet (ε ∷ []) λ {ε → here ≡.refl}
  isFiniteAt monoidCode 1 = enumerable-isFiniteSet [] λ ()
  isFiniteAt monoidCode 2 = enumerable-isFiniteSet (∙ ∷ []) λ {∙ → here ≡.refl}
  isFiniteAt monoidCode (suc (suc (suc _))) = enumerable-isFiniteSet [] λ ()

  bimonoidCode : Code _
  K bimonoidCode = BimonoidK
  boundAt bimonoidCode 0 = 2
  boundAt bimonoidCode 2 = 2
  boundAt bimonoidCode _ = 0
  isFiniteAt bimonoidCode 0 = enumerable-isFiniteSet (0# ∷ 1# ∷ []) λ {0# → here ≡.refl; 1# → there (here ≡.refl)}
  isFiniteAt bimonoidCode 1 = enumerable-isFiniteSet [] λ ()
  isFiniteAt bimonoidCode 2 = enumerable-isFiniteSet (+ ∷ * ∷ []) λ {+ → here ≡.refl; * → there (here ≡.refl)}
  isFiniteAt bimonoidCode (suc (suc (suc _))) = enumerable-isFiniteSet [] λ ()

--------------------------------------------------------------------------------
--  Subparts of bimonoids
--------------------------------------------------------------------------------

+-part : ∀ {n} → BimonoidK n → Maybe (MonoidK n)
+-part 0# = just ε
+-part + = just ∙
+-part _ = nothing

*-part : ∀ {n} → BimonoidK n → Maybe (MonoidK n)
*-part 1# = just ε
*-part * = just ∙
*-part _ = nothing

--------------------------------------------------------------------------------
--  Some named property combinations
--------------------------------------------------------------------------------

isSemigroup : Properties magmaCode
isSemigroup = fromList (associative on ∙ ∷ [])


isMonoid : Properties monoidCode
isMonoid = subΠ′ (λ {∙ → just ∙; _ → nothing}) isSemigroup
  ( ε is leftIdentity for ∙
  ∷ ε is rightIdentity for ∙
  ∷ [])


isCommutativeMonoid : Properties monoidCode
isCommutativeMonoid = subΠ just isMonoid (fromList (commutative on ∙ ∷ []))


isSemiring : Properties bimonoidCode
isSemiring =
  subΠ +-part isCommutativeMonoid (
  subΠ′ *-part isMonoid
  ( 0# is leftZero for *
  ∷ 0# is rightZero for *
  ∷ * ⟨ distributesOverˡ ⟩ₚ +
  ∷ * ⟨ distributesOverʳ ⟩ₚ +
  ∷ []
  ))

--------------------------------------------------------------------------------
--  Subcode Proofs
--------------------------------------------------------------------------------

magma⊂monoid : IsSubcode magmaCode monoidCode
magma⊂monoid .subK→supK ∙ = ∙
magma⊂monoid .supK→subK ∙ = just ∙
magma⊂monoid .supK→subK ε = nothing
magma⊂monoid .acrossSub ∙ = ≡.refl

+-monoid⊂bimonoid : IsSubcode monoidCode bimonoidCode
+-monoid⊂bimonoid .subK→supK ∙ = +
+-monoid⊂bimonoid .subK→supK ε = 0#
+-monoid⊂bimonoid .supK→subK + = just ∙
+-monoid⊂bimonoid .supK→subK 0# = just ε
+-monoid⊂bimonoid .supK→subK _ = nothing
+-monoid⊂bimonoid .acrossSub ∙ = ≡.refl
+-monoid⊂bimonoid .acrossSub ε = ≡.refl

*-monoid⊂bimonoid : IsSubcode monoidCode bimonoidCode
*-monoid⊂bimonoid .subK→supK ∙ = *
*-monoid⊂bimonoid .subK→supK ε = 1#
*-monoid⊂bimonoid .supK→subK * = just ∙
*-monoid⊂bimonoid .supK→subK 1# = just ε
*-monoid⊂bimonoid .supK→subK _ = nothing
*-monoid⊂bimonoid .acrossSub ∙ = ≡.refl
*-monoid⊂bimonoid .acrossSub ε = ≡.refl

--------------------------------------------------------------------------------
--  Conversion to structures from the agda standard library
--------------------------------------------------------------------------------

module Into {c ℓ} where
  open Algebra using (Semigroup; Monoid; CommutativeMonoid; Semiring)

  module _ (struct : Struct magmaCode c ℓ) where
    open Struct struct

    semigroup : ∀ ⦃ hasSemigroup : Hasₚ isSemigroup ⦄ → Semigroup _ _
    semigroup ⦃ hasSemigroup ⦄ = record
      { _∙_ = ⟦ ∙ ⟧
      ; isSemigroup = record
        { isEquivalence = isEquivalence
        ; assoc = from hasSemigroup (associative on ∙)
        ; ∙-cong = cong ∙
        }
      }

  module _ (struct : Struct monoidCode c ℓ) where
    open Struct struct

    monoid : ⦃ hasMonoid : Hasₚ isMonoid ⦄ → Monoid c ℓ
    monoid ⦃ hasMonoid ⦄ = record
      { isMonoid = record
        { isSemigroup = S.isSemigroup
        ; identity = from hasMonoid (ε is leftIdentity for ∙) , from hasMonoid (ε is rightIdentity for ∙)
        }
      }
      where
      magmaPart : Struct magmaCode c ℓ
      magmaPart = substruct magma⊂monoid

      module S = Semigroup (semigroup magmaPart ⦃ toSubstruct magma⊂monoid (weaken hasMonoid) ⦄)

    commutativeMonoid : ⦃ hasCommutativeMonoid : Hasₚ isCommutativeMonoid ⦄ → CommutativeMonoid c ℓ
    commutativeMonoid ⦃ hasCommutativeMonoid ⦄ = record
      { isCommutativeMonoid = record
        { isSemigroup = S.isSemigroup
        ; identityˡ = from hasCommutativeMonoid (ε is leftIdentity for ∙)
        ; comm = from hasCommutativeMonoid (commutative on ∙)
        }
      }
      where
      magmaPart : Struct magmaCode c ℓ
      magmaPart = substruct magma⊂monoid

      module S = Semigroup (semigroup magmaPart ⦃ toSubstruct magma⊂monoid (weaken hasCommutativeMonoid) ⦄)

  module _ (struct : Struct bimonoidCode c ℓ) where
    open Struct struct

    semiring : ⦃ hasSemiring : Hasₚ isSemiring ⦄ → Semiring c ℓ
    semiring ⦃ hasSemiring ⦄ = record
      { isSemiring = record
        { isSemiringWithoutAnnihilatingZero = record
          { +-isCommutativeMonoid = +-CM.isCommutativeMonoid
          ; *-isMonoid = *-M.isMonoid
          ; distrib = from hasSemiring (* ⟨ distributesOverˡ ⟩ₚ +),
                      from hasSemiring (* ⟨ distributesOverʳ ⟩ₚ +)
          }
        ; zero = from hasSemiring (0# is leftZero for *) ,
                 from hasSemiring (0# is rightZero for *)
        }
      }
      where
      +-monoidPart : Struct monoidCode c ℓ
      +-monoidPart = substruct +-monoid⊂bimonoid

      *-monoidPart : Struct monoidCode c ℓ
      *-monoidPart = substruct *-monoid⊂bimonoid

      module +-CM = CommutativeMonoid (commutativeMonoid +-monoidPart ⦃ toSubstruct +-monoid⊂bimonoid (weaken hasSemiring) ⦄)
      module *-M = Monoid (monoid *-monoidPart ⦃ toSubstruct *-monoid⊂bimonoid (weaken hasSemiring) ⦄)
