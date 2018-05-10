open import MLib.Algebra.PropertyCode

module MLib.Algebra.PropertyCode.Dependent {k c ℓ} {code : Code k} (struct : Struct code c ℓ) where

open import MLib.Prelude
open import MLib.Algebra.PropertyCode.Core

open import Function.Equivalence using (Equivalence)

open Struct struct

private
  module FuncBased {c′ ℓ′} (depRawStruct : RawStruct K c′ ℓ′) (props : ∀ π → Maybe (∃ λ deps → ⦃ _ : Hasₚ deps ⦄ → ⟦ π ⟧P depRawStruct)) where
    Π′ : Properties code
    Π′ = properties λ π →
      case props π of λ
      { (just (deps , _)) → implies deps Π
      ; nothing → false
      }

    Π′-prop : ∀ {π} → π ∈ₚ Π′ → ∃ λ x → props π ≡ just x
    Π′-prop {π} π∈Π′ with props π | ≡.inspect props π
    Π′-prop {π} π∈Π′ | just x | _ = x , ≡.refl
    Π′-prop {π} (fromTruth truth) | nothing | ≡.[ eq ] rewrite eq = ⊥-elim truth

    reify′ : ∀ {π} → π ∈ₚ Π′ → ⟦ π ⟧P depRawStruct
    reify′ {π} π∈Π′ with Π′-prop π∈Π′ | hasProperty Π′ π | ≡.inspect (hasProperty Π′) π
    reify′ {_} (fromTruth truth) | (deps , f) , eq | false | ≡.[ eq₁ ] rewrite eq | eq₁ = ⊥-elim truth
    reify′ {_} (fromTruth truth) | (deps , f) , eq | true | ≡.[ eq₁ ] rewrite eq = f ⦃ fromTruth truth  ⦄

    dependentStruct :
      Struct code c′ ℓ′
    dependentStruct = record
      { rawStruct = depRawStruct
      ; Π = Π′
      ; reify = reify′
      }

  module ListBased {c′ ℓ′} (depRawStruct : RawStruct K c′ ℓ′) (props : List (∃₂ λ π deps → ⦃ _ : Hasₚ deps ⦄ → ⟦ π ⟧P depRawStruct)) where
    Func = ∀ π → Maybe (∃ (λ deps → ⦃ _ : Hasₚ deps ⦄ → ⟦ π ⟧P depRawStruct))

    singleFunc : (∃₂ λ π deps → ⦃ _ : Hasₚ deps ⦄ → ⟦ π ⟧P depRawStruct) → Func
    singleFunc (π , deps , f) π′ with π Property.≟ π′
    singleFunc (π , deps , f) π′ | yes p rewrite Property.≈⇒≡ p = just (deps , f)
    singleFunc (π , deps , f) π′ | no _ = nothing

    combineFuncs : Func → Func → Func
    combineFuncs f g π =
      case f π of λ
      { (just r) → just r
      ; nothing → case g π of λ
        { (just r) → just r
        ; nothing → nothing
        }
      }

    propsF : ∀ π → Maybe (∃ (λ deps → ⦃ _ : Hasₚ deps ⦄ → ⟦ π ⟧P depRawStruct))
    propsF = List.foldr combineFuncs (λ _ → nothing) (List.map singleFunc props)

    dependentStruct : Struct code c′ ℓ′
    dependentStruct = FuncBased.dependentStruct depRawStruct propsF

open ListBased using (dependentStruct) public
