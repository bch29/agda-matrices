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

  fromParts : Σ (Fin numParts) (Fin ∘ sizeAt) → Fin totalSize
  fromParts (i , j) = fromℕ≤ {PN.fromParts (toℕ i , toℕ j)} (PN.fromParts-prop (Fin.bounded i) (bounded′ j))

  toParts : Fin totalSize → Σ (Fin numParts) (Fin ∘ sizeAt)
  toParts k =
    let p , q = PN.toParts-prop (Fin.bounded k)
    in fromℕ≤ p , fromℕ≤ q

  abstract
    fromParts-fromPartsℕ : (i : Fin numParts) (j : Fin (sizeAt i)) → toℕ (fromParts (i , j)) ≡ PN.fromParts (toℕ i , toℕ j)
    fromParts-fromPartsℕ _ _ = Fin.toℕ-fromℕ≤ _

    toParts-toPartsℕ : (k : Fin totalSize) → Σ.map toℕ toℕ (toParts k) ≡ PN.toParts (toℕ k)
    toParts-toPartsℕ k = Σ.≡×≡⇒≡ (Fin.toℕ-fromℕ≤ _ , Fin.toℕ-fromℕ≤ _)

    toParts-fromParts : ∀ {i j} → toParts (fromParts (i , j)) ≡ (i , j)
    toParts-fromParts {i} {j} = Fin.toℕ-injective₂ (begin
      Σ.map toℕ toℕ (toParts (fromParts (i , j)))   ≡⟨ toParts-toPartsℕ _ ⟩
      PN.toParts (toℕ (fromParts (i , j)))          ≡⟨ ≡.cong PN.toParts (fromParts-fromPartsℕ i j) ⟩
      PN.toParts (PN.fromParts (toℕ i , toℕ j))    ≡⟨ PN.toParts-fromParts (Fin.bounded i) (bounded′ j) ⟩
      (toℕ i , toℕ j)                                 ∎)
      where open ≡.Reasoning

    fromParts-toParts : ∀ {k} → fromParts (toParts k) ≡ k
    fromParts-toParts {k} = Fin.toℕ-injective (
      begin
        toℕ (fromParts (toParts k))               ≡⟨ uncurry fromParts-fromPartsℕ (toParts k) ⟩
        PN.fromParts (Σ.map toℕ toℕ (toParts k))  ≡⟨ ≡.cong PN.fromParts (toParts-toPartsℕ k) ⟩
        PN.fromParts (PN.toParts (toℕ k))         ≡⟨ PN.fromParts-toParts (toℕ k) (Fin.bounded k) ⟩
        toℕ k                                       ∎)
      where open ≡.Reasoning

  asParts : Fin totalSize ↔ Σ (Fin numParts) (Fin ∘ sizeAt)
  asParts = record
    { to = ≡.→-to-⟶ toParts
    ; from = ≡.→-to-⟶ fromParts
    ; inverse-of = record
      { left-inverse-of = λ _ → fromParts-toParts
      ; right-inverse-of = λ _ → toParts-fromParts
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

    fromParts² : (j : Fin P₂.numParts) → Fin (size (P₂.partAt j)) → Fin P₁.totalSize
    fromParts² j = curry P₁.fromParts i ∘ curry P₂.fromParts j

  asParts² :
    Fin P₁.totalSize ↔
    Σ (Fin P₁.numParts) (λ i →
      let P₂ = P₁.partAt i
          module P₂ = Parts P₂
      in Σ (Fin P₂.numParts) (Fin ∘ P₂.sizeAt))
  asParts² =
    Fin P₁.totalSize ↔⟨ P₁.asParts ⟩
    Σ (Fin P₁.numParts) (Fin ∘ P₁.sizeAt) ↔⟨ Σ-bij (Parts.asParts ∘ P₁.partAt) ⟩
    Σ (Fin P₁.numParts) (λ i →
      let P₂ = P₁.partAt i
          module P₂ = Parts P₂
      in Σ (Fin P₂.numParts) (Fin ∘ P₂.sizeAt)) ∎
    where open BijReasoning
