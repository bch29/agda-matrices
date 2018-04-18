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
open Nat using (suc; zero)
open import Data.Vec.Relation.Pointwise.Inductive using (_∷_; [])

open import Function.LeftInverse using (LeftInverse; _↞_)
open import Function.Equality using (_⟨$⟩_) renaming (cong to feCong)

open import Category.Applicative

--------------------------------------------------------------------------------
--  Some named property combinations
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

  private
    magma↞monoid2 : MagmaK 2 ↞ MonoidK 2
    magma↞monoid2 .to ._⟨$⟩_ ∙ = ∙
    magma↞monoid2 .to .feCong ≡.refl = ≡.refl
    magma↞monoid2 .from ._⟨$⟩_ ∙ = ∙
    magma↞monoid2 .from .feCong ≡.refl = ≡.refl
    magma↞monoid2 .left-inverse-of ∙ = ≡.refl

  magmaSubcodeMonoid : IsSubcode magmaCode monoidCode
  magmaSubcodeMonoid 0 = inj₁ λ ()
  magmaSubcodeMonoid 1 = inj₁ λ ()
  magmaSubcodeMonoid 2 = inj₂ magma↞monoid2
  magmaSubcodeMonoid (suc (suc (suc _))) = inj₁ λ ()

  private
    monoid↞bimonoid0 : MonoidK 0 ↞ BimonoidK 0
    monoid↞bimonoid0 .to ._⟨$⟩_ ε = 0#
    monoid↞bimonoid0 .to .feCong ≡.refl = ≡.refl
    monoid↞bimonoid0 .from ._⟨$⟩_ 0# = ε
    monoid↞bimonoid0 .from ._⟨$⟩_ 1# = ε
    monoid↞bimonoid0 .from .feCong ≡.refl = ≡.refl
    monoid↞bimonoid0 .left-inverse-of ε = ≡.refl

    monoid↞bimonoid2 : MonoidK 2 ↞ BimonoidK 2
    monoid↞bimonoid2 .to ._⟨$⟩_ ∙ = +
    monoid↞bimonoid2 .to .feCong ≡.refl = ≡.refl
    monoid↞bimonoid2 .from ._⟨$⟩_ + = ∙
    monoid↞bimonoid2 .from ._⟨$⟩_ * = ∙
    monoid↞bimonoid2 .from .feCong ≡.refl = ≡.refl
    monoid↞bimonoid2 .left-inverse-of ∙ = ≡.refl

  monoidSubcodeBimonoid : IsSubcode monoidCode bimonoidCode
  monoidSubcodeBimonoid 0 = inj₂ monoid↞bimonoid0
  monoidSubcodeBimonoid 1 = inj₁ λ ()
  monoidSubcodeBimonoid 2 = inj₂ monoid↞bimonoid2
  monoidSubcodeBimonoid (suc (suc (suc _))) = inj₁ λ ()

module Into {c ℓ} where
  open Algebra using (Semigroup; Monoid; CommutativeMonoid; Semiring)

  module _ (struct : Struct magmaCode c ℓ) where
    open Struct struct

    semigroup : ∀ ⦃ hasSemigroup : HasEach isSemigroup ⦄ → Semigroup _ _
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

    monoid : ⦃ hasMonoid : HasEach isMonoid ⦄ → Monoid c ℓ
    monoid ⦃ hasMonoid ⦄ = record
      { ε = ⟦ ε ⟧
      ; isMonoid = record
        { isSemigroup = S.isSemigroup
        ; identity = from hasMonoid (ε is leftIdentity for ∙) , from hasMonoid (ε is rightIdentity for ∙)
        }
      }
      where
        magmaPart : Struct magmaCode c ℓ
        magmaPart = subStruct magmaSubcodeMonoid

        module S = Semigroup (semigroup magmaPart ⦃ inSubStruct magmaSubcodeMonoid {Π′ = supcodeProperties magmaSubcodeMonoid ?} {!get hasMonoid ⦃ ? ⦄!} ⦄)

  module _ (struct : Struct bimonoidCode c ℓ) where
    open Struct struct

    monoidStruct : Struct monoidCode c ℓ
    monoidStruct = subStruct monoidSubcodeBimonoid

    semiring : ⦃ hasSemiring : HasEach isSemiring ⦄ → Semiring c ℓ
    semiring ⦃ hasSemiring ⦄ = record
      { _≈_ = _≈_
      ; _+_ = ⟦ + ⟧
      ; _*_ = ⟦ * ⟧
      ; 0# = ⟦ 0# ⟧
      ; 1# = ⟦ 1# ⟧
      ; isSemiring = record
        { isSemiringWithoutAnnihilatingZero = record
          { +-isCommutativeMonoid = record
            { isSemigroup = record
              { isEquivalence = isEquivalence
              ; assoc = from hasSemiring (associative on +)
              ; ∙-cong = cong +
              }
            ; identityˡ = from hasSemiring (0# is leftIdentity for +)
            ; comm = from hasSemiring (commutative on +)
            }
          ; *-isMonoid = record
            { isSemigroup = record
              { isEquivalence = isEquivalence
              ; assoc = from hasSemiring (associative on *)
              ; ∙-cong = cong *
              }
            ; identity = from hasSemiring (1# is leftIdentity for *) ,
                         from hasSemiring (1# is rightIdentity for *)
            }
          ; distrib = from hasSemiring (* ⟨ distributesOverˡ ⟩ₚ +),
                      from hasSemiring (* ⟨ distributesOverʳ ⟩ₚ +)
          }
        ; zero = from hasSemiring (0# is leftZero for *) ,
                 from hasSemiring (0# is rightZero for *)
        }
      }
