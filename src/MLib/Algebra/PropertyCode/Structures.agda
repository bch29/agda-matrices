module MLib.Algebra.PropertyCode.Structures where

open import MLib.Prelude
open import MLib.Prelude.Finite
open import MLib.Algebra.Instances

open import MLib.Algebra.PropertyCode.RawStruct public
open import MLib.Algebra.PropertyCode.Core public

open import Relation.Binary as B using (Setoid)

open List using (_∷_; [])
open import Data.List.All as All using (All; _∷_; []) public
open import Data.List.Any using (Any; here; there)
open import Data.Bool using (_∨_)

open import Category.Applicative

--------------------------------------------------------------------------------
--  Some named property combinations
--------------------------------------------------------------------------------

private
  traverseAll : ∀ {a p p′} {A : Set a} {P : A → Set p} {P′ : A → Set p′} → (∀ {x} → P x → Maybe (P′ x)) → {xs : List A} → All P xs → Maybe (All P′ xs)
  traverseAll f [] = just []
  traverseAll f (px ∷ ap) with f px | traverseAll f ap
  traverseAll f (px ∷ ap) | just px′ | just ap′ = just (px′ ∷ ap′)
  traverseAll f (px ∷ ap) | _ | _ = nothing

subΠ : ∀ {k k′} {code : Code k} {code′ : Code k′} →
  let open Code code using (K)
      open Code code′ using () renaming (K to K′)
  in (∀ {n} → K′ n → Maybe (K n)) →
     Properties code → Properties code′ → Properties code′
hasProperty (subΠ f Π₀ Π₁) (π , κs) = hasProperty Π₁ (π , κs) ∨ satUnder
  where
    satUnder : Bool
    satUnder with traverseAll f κs
    satUnder | just κs′ = hasProperty Π₀ (π , κs′)
    satUnder | nothing = false

subΠ′ : ∀ {k k′} {code : Code k} {code′ : Code k′} →
  let open Code code using (K)
      open Code code′ using () renaming (K to K′)
  in (∀ {n} → K′ n → Maybe (K n)) →
     Properties code → List (Property K′) → Properties code′
subΠ′ f Π πs = subΠ f Π (fromList πs)

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
  open Nat using (suc)

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


+-part : ∀ {n} → BimonoidK n → Maybe (MonoidK n)
+-part 0# = just ε
+-part + = just ∙
+-part _ = nothing

*-part : ∀ {n} → BimonoidK n → Maybe (MonoidK n)
*-part 1# = just ε
*-part * = just ∙
*-part _ = nothing


open PropertyC using (_on_; _is_for_; _⟨_⟩ₚ_)

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

--   monoid : ∀ {c ℓ} {props} ⦃ _ : isMonoid ⊆ props ⦄ → Dagma props c ℓ → Monoid c ℓ
--   monoid ⦃ mon ⦄ dagma = record
--     { isMonoid = record
--       { isSemigroup = S.isSemigroup
--       ; identity = proj₂ (from isMonoid hasIdentity)
--       }
--     }
--     where
--       open Dagma dagma
--       module S = Semigroup (semigroup (dagma ↓M isMonoid ↓M isSemigroup))

--   commutativeMonoid : ∀ {c ℓ} {props} ⦃ _ : isCommutativeMonoid ⊆ props ⦄ → Dagma props c ℓ → CommutativeMonoid c ℓ
--   commutativeMonoid dagma = record
--     { isCommutativeMonoid = record
--       { isSemigroup = S.isSemigroup
--       ; leftIdentity = proj₁ (proj₂ (from isCommutativeMonoid hasIdentity))
--       ; comm = from isCommutativeMonoid commutative
--       }
--     }
--     where
--       open Dagma dagma
--       module S = Semigroup (semigroup (dagma ↓M isCommutativeMonoid ↓M isSemigroup))

--   -- semiring
