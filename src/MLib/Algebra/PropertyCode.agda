module MLib.Algebra.PropertyCode where

open import MLib.Prelude
open import MLib.Prelude.Finite
open import MLib.Algebra.Instances

open import MLib.Algebra.PropertyCode.RawStruct public
open import MLib.Algebra.PropertyCode.Core public

import Relation.Unary as U using (Decidable)
open import Relation.Binary as B using (Setoid)
open import Function.LeftInverse using (LeftInverse; _↞_)
open import Function.Equality as FE using (_⟨$⟩_)

open List using (_∷_; [])
open import Data.List.All as All using (All; _∷_; []) public
open import Data.List.Any using (Any; here; there)
open import Data.Bool using (_∨_)
open import Data.Vec using ([]; _∷_)
open import Data.Vec.Relation.Pointwise.Inductive using ([]; _∷_)

open import Category.Applicative

record Struct {k} (code : Code k) c ℓ : Set (sucˡ (c ⊔ˡ ℓ ⊔ˡ k)) where
  open Code code public

  field
    rawStruct : RawStruct K c ℓ
    Π : Properties code

  open RawStruct rawStruct public

  open Properties Π public

  field
    reify : ∀ {π} → π ∈ₚ Π → ⟦ π ⟧P rawStruct

  HasEach : (Π′ : Properties code) → Set
  HasEach Π′ = Π′ ⇒ₚ Π

  HasList : List (Property K) → Set
  HasList = HasEach ∘ fromList

  Has : Property K → Set
  Has π = HasEach (singleton π)

  use : ∀ π ⦃ hasπ : π ∈ₚ Π ⦄ → ⟦ π ⟧P rawStruct
  use _ ⦃ hasπ ⦄ = reify hasπ

  from : ∀ {Π′} (hasΠ′ : HasEach Π′) π ⦃ hasπ : π ∈ₚ Π′ ⦄ → ⟦ π ⟧P rawStruct
  from hasΠ′ _ ⦃ hasπ ⦄ = use _ ⦃ ⇒ₚ-MP hasπ hasΠ′ ⦄

  get : ∀ {Π′ Π′′} (hasΠ′ : HasEach Π′) ⦃ hasΠ′′ : Π′′ ⇒ₚ Π′ ⦄ → HasEach Π′′
  get hasΠ′ ⦃ hasΠ′′ ⦄ = ⇒ₚ-trans hasΠ′′ hasΠ′

  private
    transferCongⁿ : ∀ {k′} {code′ : Code k′} (isSub : IsSubcode code′ code) → ∀ {n} (κ : Code.K code′ n) → Congruentₙ _≈_ ((appOp ∘ subK→supK {sub = code′} {sup = code} isSub) κ)
    transferCongⁿ isSub {n} κ = congⁿ (subK→supK isSub κ)

  subStruct : ∀ {k′} {code′ : Code k′} → IsSubcode code′ code → Struct code′ c ℓ
  subStruct isSub = record
    { rawStruct = record
      { Carrier = Carrier
      ; _≈_ = _≈_
      ; appOp = appOp ∘ subK→supK isSub
      ; isRawStruct = isRawStruct′
      }
    ; Π = subcodeProperties isSub Π
    ; reify = reinterpret isSub rawStruct isRawStruct′ _ ∘ reify ∘ fromSubcode isSub
    }
    where
    isRawStruct′ = record
      { isEquivalence = isEquivalence
      ; congⁿ = transferCongⁿ isSub
      }

  inSubStruct :
    ∀ {k′} {code′ : Code k′} (isSub : IsSubcode code′ code) →
    ∀ {Π′ : Properties code′} (hasΠ′ : HasEach (supcodeProperties isSub Π′)) →
    Π′ ⇒ₚ subcodeProperties isSub Π
  inSubStruct isSub hasΠ′ = →ₚ-⇒ₚ λ π hasπ → fromSupcode isSub (⇒ₚ-→ₚ hasΠ′ (mapProperty (subK→supK isSub) π) (fromSupcode′ isSub hasπ))
