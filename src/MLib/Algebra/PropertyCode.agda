module MLib.Algebra.PropertyCode where

open import MLib.Prelude
open import MLib.Finite

open import MLib.Algebra.PropertyCode.RawStruct public
open import MLib.Algebra.PropertyCode.Core as Core public
  using (Property; Properties; Code; IsSubcode; _∈ₚ_; _⇒ₚ_; ⟦_⟧P)
  renaming (⇒ₚ-narrow to narrow)

open Core.PropKind public
open Core.PropertyC using (_on_; _is_for_; _⟨_⟩ₚ_) public

import Relation.Unary as U using (Decidable)
open import Relation.Binary as B using (Setoid)

open import Data.List.All as All using (All; _∷_; []) public
open import Data.List.Any using (Any; here; there)
open import Data.Bool using (_∨_)

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

  Hasₚ : (Π′ : Properties code) → Set
  Hasₚ Π′ = Π′ ⇒ₚ Π

  Has : List (Property K) → Set
  Has = Hasₚ ∘ Core.fromList

  Has₁ : Property K → Set
  Has₁ π = Hasₚ (Core.singleton π)

  use : ∀ π ⦃ hasπ : π ∈ₚ Π ⦄ → ⟦ π ⟧P rawStruct
  use _ ⦃ hasπ ⦄ = reify hasπ

  from : ∀ {Π′} (hasΠ′ : Hasₚ Π′) π ⦃ hasπ : π ∈ₚ Π′ ⦄ → ⟦ π ⟧P rawStruct
  from hasΠ′ _ ⦃ hasπ ⦄ = use _ ⦃ Core.⇒ₚ-MP hasπ hasΠ′ ⦄

  substruct : ∀ {k′} {code′ : Code k′} → IsSubcode code′ code → Struct code′ c ℓ
  substruct isSub = record
    { rawStruct = record
      { Carrier = Carrier
      ; _≈_ = _≈_
      ; appOp = appOp ∘ Core.subK→supK isSub
      ; isRawStruct = isRawStruct′
      }
    ; Π = Core.subcodeProperties isSub Π
    ; reify = Core.reinterpret isSub rawStruct isRawStruct′ _ ∘ reify ∘ Core.fromSubcode isSub
    }
    where
    isRawStruct′ = record
      { isEquivalence = isEquivalence
      ; congⁿ = congⁿ ∘ Core.subK→supK isSub
      }

  toSubstruct :
    ∀ {k′} {code′ : Code k′} (isSub : IsSubcode code′ code) →
    ∀ {Π′ : Properties code′} (hasΠ′ : Hasₚ (Core.supcodeProperties isSub Π′)) →
    Π′ ⇒ₚ Core.subcodeProperties isSub Π
  toSubstruct isSub hasΠ′ = Core.→ₚ-⇒ₚ λ π hasπ →
    Core.fromSupcode isSub
      (Core.⇒ₚ-→ₚ hasΠ′
        (Core.mapProperty (Core.subK→supK isSub) π)
        (Core.fromSupcode′ isSub hasπ))
