module MLib.Algebra.PropertyCode where

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

record Struct {k} (code : Code k) c ℓ : Set (sucˡ (c ⊔ˡ ℓ ⊔ˡ k)) where
  open Code code public

  field
    rawStruct : RawStruct K c ℓ
    Π : Properties code

  open RawStruct rawStruct public

  open Properties Π public

  field
    reify : ∀ {π} → π ∈ₚ Π → ⟦ π ⟧P rawStruct

  Has : Property K → Set
  Has π = π ∈ₚ Π

  record HasEach (Π′ : Properties code) : Set where
    constructor mkHasEach
    field
      getHasEach : ⊨ (Π′ ⇒ₚ Π)

  open HasEach

  HasList : List (Property K) → Set
  HasList = HasEach ∘ fromList

  use : ∀ π ⦃ hasπ : Has π ⦄ → ⟦ π ⟧P rawStruct
  use _ ⦃ hasπ ⦄ = reify hasπ

  from : ∀ Π′ π ⦃ hasΠ′ : HasEach Π′ ⦄ ⦃ hasπ : π ∈ₚ Π′ ⦄ → ⟦ π ⟧P rawStruct
  from _ _ ⦃ hasΠ′ ⦄ ⦃ hasπ ⦄ = use _ ⦃ Has⇒ₚ hasπ (getHasEach hasΠ′) ⦄

  from′ : ∀ πs π ⦃ hasπs : HasList πs ⦄ ⦃ hasπ : π ∈ₚ fromList πs ⦄ → ⟦ π ⟧P rawStruct
  from′ _ = from _

  -- subStruct : ∀ {k′} (code′ : ∀ {n} → K n → Set k′) → Struct (λ n → Σ (K n) K′) c ℓ
