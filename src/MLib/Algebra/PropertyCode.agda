module MLib.Algebra.PropertyCode where

open import MLib.Prelude
open import MLib.Prelude.Finite
open import MLib.Algebra.Instances

open import MLib.Algebra.PropertyCode.RawStruct public
open import MLib.Algebra.PropertyCode.Core public
open import MLib.Algebra.PropertyCode.Reflection

import Relation.Unary as U using (Decidable)
open import Relation.Binary as B using (Setoid)
open import Function.LeftInverse using (LeftInverse)
open import Function.Equality as FE using (_⟨$⟩_)

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

  HasEach : (Π′ : Properties code) → Set
  HasEach Π′ = Π′ ⇒ₚ Π

  HasList : List (Property K) → Set
  HasList = HasEach ∘ fromList

  Has : Property K → Set
  Has π = HasEach (singleton π)

  -- use : ∀ π ⦃ hasπ : Has π ⦄ → ⟦ π ⟧P rawStruct
  -- use _ ⦃ hasπ ⦄ = reify hasπ

  -- from : ∀ Π′ π ⦃ hasΠ′ : HasEach Π′ ⦄ ⦃ hasπ : π ∈ₚ Π′ ⦄ → ⟦ π ⟧P rawStruct
  -- from _ _ ⦃ hasΠ′ ⦄ ⦃ hasπ ⦄ = use _ ⦃ ⇒ₚ-MP hasπ hasΠ′ ⦄

  -- from′ : ∀ πs π ⦃ hasπs : HasList πs ⦄ ⦃ hasπ : π ∈ₚ fromList πs ⦄ → ⟦ π ⟧P rawStruct
  -- from′ _ = from _

  module Macros = UseProperty rawStruct reify

  -- subStruct : ∀ {k′} {K′ : ℕ → Set k′} (inj : ∀ {n} → LeftInverse (≡.setoid (K′ n)) (K.setoid n)) → Struct (subCode inj) c ℓ
  -- subStruct {K′ = K′} inj = record
  --   { rawStruct = subRawStruct f
  --   ; Π = subCodeProperties Π inj
  --   ; reify =
  --     λ {π} → reinterpret {code = code} rawStruct (_⟨$⟩_ (LeftInverse.to inj)) π
  --           ∘ reify
  --           ∘ fromSubCode inj
  --   }
  --   where
  --     f : ∀ {n} → K′ n → K n
  --     f = _⟨$⟩_ (LeftInverse.to inj)
