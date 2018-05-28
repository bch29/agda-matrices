module MLib.Fin.Parts where

open import MLib.Prelude
open import MLib.Prelude.RelProps
import MLib.Fin.Parts.Core as C
open import MLib.Fin.Parts.Nat

open import Function.Surjection using (_↠_)
open import Function.Related renaming (module EquationalReasoning to BijReasoning)

import Relation.Binary.Indexed as I

open Nat using (_*_; _+_; _<_)
open Fin using (toℕ; fromℕ≤)
open Table

open C using (Parts; constParts) hiding (module Parts) public

module Parts {a} {A : Set a} {size : A → ℕ} (P : Parts A size) where
  open C.Parts P public
  module PN = Partsℕ P

  -- Fin functions

  private
    bounded′ : ∀ {i} (j : Fin (sizeAt i)) → toℕ j < PN.sizeAt (fromℕ≤ (Fin.bounded i))
    bounded′ j = Nat.≤-trans (Fin.bounded j) (Nat.≤-reflexive (≡.sym (≡.cong sizeAt (Fin.fromℕ≤-toℕ _ _))))

  intoPart : Σ (Fin numParts) (Fin ∘ sizeAt) → Fin totalSize
  intoPart (i , j) = fromℕ≤ {PN.intoPart (toℕ i , toℕ j)} (PN.intoPart-prop (Fin.bounded i) (bounded′ j))

  fromPart : Fin totalSize → Σ (Fin numParts) (Fin ∘ sizeAt)
  fromPart k =
    let p , q = PN.fromPart-prop (Fin.bounded k)
    in fromℕ≤ p , fromℕ≤ q

  abstract
    intoPart-intoPartℕ : (i : Fin numParts) (j : Fin (sizeAt i)) → toℕ (intoPart (i , j)) ≡ PN.intoPart (toℕ i , toℕ j)
    intoPart-intoPartℕ _ _ = Fin.toℕ-fromℕ≤ _

    fromPart-fromPartℕ : (k : Fin totalSize) → Σ.map toℕ toℕ (fromPart k) ≡ PN.fromPart (toℕ k)
    fromPart-fromPartℕ k = Σ.≡×≡⇒≡ (Fin.toℕ-fromℕ≤ _ , Fin.toℕ-fromℕ≤ _)

    fromPart-intoPart : ∀ {i j} → fromPart (intoPart (i , j)) ≡ (i , j)
    fromPart-intoPart {i} {j} = Fin.toℕ-injective₂ (begin
      Σ.map toℕ toℕ (fromPart (intoPart (i , j)))   ≡⟨ fromPart-fromPartℕ _ ⟩
      PN.fromPart (toℕ (intoPart (i , j)))          ≡⟨ ≡.cong PN.fromPart (intoPart-intoPartℕ i j) ⟩
      PN.fromPart (PN.intoPart (toℕ i , toℕ j))    ≡⟨ PN.fromPart-intoPart (Fin.bounded i) (bounded′ j) ⟩
      (toℕ i , toℕ j)                                 ∎)
      where open ≡.Reasoning

    intoPart-fromPart : ∀ {k} → intoPart (fromPart k) ≡ k
    intoPart-fromPart {k} = Fin.toℕ-injective (
      begin
        toℕ (intoPart (fromPart k))               ≡⟨ uncurry intoPart-intoPartℕ (fromPart k) ⟩
        PN.intoPart (Σ.map toℕ toℕ (fromPart k))  ≡⟨ ≡.cong PN.intoPart (fromPart-fromPartℕ k) ⟩
        PN.intoPart (PN.fromPart (toℕ k))         ≡⟨ PN.intoPart-fromPart (toℕ k) (Fin.bounded k) ⟩
        toℕ k                                       ∎)
      where open ≡.Reasoning

  asPart : Σ (Fin numParts) (Fin ∘ sizeAt) ↔ Fin totalSize
  asPart = record
    { to = ≡.→-to-⟶ intoPart
    ; from = ≡.→-to-⟶ fromPart
    ; inverse-of = record
      { left-inverse-of = λ _ → fromPart-intoPart
      ; right-inverse-of = λ _ → intoPart-fromPart
      }
    }

Parts² : ∀ {a} (A : Set a) (size : A → ℕ) → Set a
Parts² A size = Parts (Parts A size) Parts.totalSize

module _ {a} {A : Set a} {size : A → ℕ} (P₁ : Parts² A size) where
  private
    module P₁ = Parts P₁

  module _ (i : Fin P₁.numParts) where
    private
      P₂ = P₁.partAt i
      module P₂ = Parts P₂

    intoPart² : (j : Fin P₂.numParts) → Fin (size (P₂.partAt j)) → Fin P₁.totalSize
    intoPart² j = curry P₁.intoPart i ∘ curry P₂.intoPart j

  asPart² :
    Σ (Fin P₁.numParts) (λ i →
      let P₂ = P₁.partAt i
          module P₂ = Parts P₂
      in Σ (Fin P₂.numParts) (Fin ∘ P₂.sizeAt))
    ↔ Fin P₁.totalSize
  asPart² =
      Σ (Fin P₁.numParts) (λ i →
        let P₂ = P₁.partAt i
            module P₂ = Parts P₂
        in Σ (Fin P₂.numParts) (Fin ∘ P₂.sizeAt))
    ↔⟨ Σ-bij (Parts.asPart ∘ P₁.partAt) ⟩
      Σ (Fin P₁.numParts) (Fin ∘ P₁.sizeAt)
    ↔⟨ P₁.asPart ⟩
      Fin P₁.totalSize
    ∎
    where open BijReasoning
