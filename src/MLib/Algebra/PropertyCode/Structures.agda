module MLib.Algebra.PropertyCode.Structures where

open import MLib.Prelude
open import MLib.Prelude.Finite
open import MLib.Algebra.Instances

open import MLib.Algebra.PropertyCode.RawStruct public
open import MLib.Algebra.PropertyCode.Core public
open import MLib.Algebra.PropertyCode public

open import Relation.Binary as B using (Setoid)

open List using (_∷_; [])
open import Data.List.Any using (Any; here; there)
open import Data.Bool using (_∨_)
open import Data.Vec.Relation.Pointwise.Inductive using (_∷_; [])

open import Function.LeftInverse using (LeftInverse; _↞_)
open import Function.Equality using (_⟨$⟩_) renaming (cong to feCong)

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

module _ {k k′} {code : Code k} {code′ : Code k′} where
  private
    module K = Code code
    module K′ = Code code′
    open K using (K)
    open K′ using () renaming (K to K′)

    liftK : (∀ {n} → K′ n → Maybe (K n)) → {ns : List ℕ} → All K′ ns → Maybe (All K ns)
    liftK f [] = just []
    liftK f (px ∷ ak) with f px | liftK f ak
    liftK f (px ∷ ak) | just px′ | just ak′ = just (px′ ∷ ak′)
    liftK f (px ∷ ak) | _ | _ = nothing

    liftπ : (∀ {n} → K′ n → Maybe (K n)) → Property K′ → Maybe (Property K)
    liftπ f (π , κs) with liftK f κs
    liftπ f (π , κs) | just κs′ = just (π , κs′)
    liftπ f (π , κs) | nothing = nothing

  liftΠ : (∀ {n} → K′ n → Maybe (K n)) → Properties code → Properties code′
  hasProperty (liftΠ f Π) π with liftπ f π
  hasProperty (liftΠ f Π) π | just π′ = hasProperty Π π′
  hasProperty (liftΠ f Π) π | nothing = false

module _ where
  open LeftInverse

  magma↞monoid : ∀ {n} → Maybe (MagmaK n) ↞ Maybe (MonoidK n)
  magma↞monoid .to ._⟨$⟩_ (just ∙) = just ∙
  magma↞monoid .to ._⟨$⟩_ nothing = nothing
  magma↞monoid .to .feCong ≡.refl = ≡.refl
  magma↞monoid .from ._⟨$⟩_ (just ε) = nothing
  magma↞monoid .from ._⟨$⟩_ (just ∙) = just ∙
  magma↞monoid .from ._⟨$⟩_ nothing = nothing
  magma↞monoid .from .feCong ≡.refl = ≡.refl
  magma↞monoid .left-inverse-of (just ∙) = ≡.refl
  magma↞monoid .left-inverse-of nothing = ≡.refl

-- module Into {c ℓ} where
--   open Algebra using (Semigroup; Monoid; CommutativeMonoid)

--   module _ (struct : Struct magmaCode c ℓ) where
--     open Struct struct

--     semigroup : ∀ {Π : Properties magmaCode} ⦃ hasSemigroup : HasEach isSemigroup ⦄ → Semigroup _ _
--     semigroup = record
--       { _∙_ = ⟦ ∙ ⟧
--       ; isSemigroup = record
--         { isEquivalence = isEquivalence
--         ; assoc = from isSemigroup (associative on ∙)
--         ; ∙-cong = λ p q → congⁿ ∙ (p ∷ q ∷ [])
--         }
--       }

  -- module _ (struct : Struct monoidCode c ℓ) where
  --   open Struct struct

  --   monoid : ∀ {c ℓ} ⦃ _ : HasEach isMonoid ⦄ → Monoid c ℓ
  --   monoid ⦃ mon ⦄ = record
  --     { isMonoid = record
  --       { isSemigroup = {!!}
  --       ; identity = {!!}
  --       }
  --     }
  --     where
  --       magmaPart : Struct (subCode magma↞monoid) c ℓ
  --       magmaPart = subStruct magma↞monoid

  --       module S = Semigroup (semigroup {!!})

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
