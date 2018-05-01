module MLib.Fin.Pieces where

open import MLib.Prelude
open import MLib.Prelude.RelProps
import MLib.Fin.Pieces.Core as C
open import MLib.Fin.Pieces.Nat

open import Function.Surjection using (_↠_)
open import Function.Related renaming (module EquationalReasoning to BijReasoning)

import Relation.Binary.Indexed as I

open Nat using (_*_; _+_; _<_)
open Fin using (toℕ; fromℕ≤)
open Table

open C using (Pieces; constPieces) hiding (module Pieces) public

module Pieces {a} {A : Set a} {size : A → ℕ} (P : Pieces A size) where
  open C.Pieces P public
  module PN = Piecesℕ P

  -- Fin functions

  private
    bounded′ : ∀ {i} (j : Fin (sizeAt i)) → toℕ j < PN.sizeAt (fromℕ≤ (Fin.bounded i))
    bounded′ j = Nat.≤-trans (Fin.bounded j) (Nat.≤-reflexive (≡.sym (≡.cong sizeAt (Fin.fromℕ≤-toℕ _ _))))

  intoPiece : Σ (Fin numPieces) (Fin ∘ sizeAt) → Fin totalSize
  intoPiece (i , j) = fromℕ≤ {PN.intoPiece (toℕ i , toℕ j)} (PN.intoPiece-prop (Fin.bounded i) (bounded′ j))

  fromPiece : Fin totalSize → Σ (Fin numPieces) (Fin ∘ sizeAt)
  fromPiece k =
    let p , q = PN.fromPiece-prop (Fin.bounded k)
    in fromℕ≤ p , fromℕ≤ q

  abstract
    intoPiece-intoPieceℕ : (i : Fin numPieces) (j : Fin (sizeAt i)) → toℕ (intoPiece (i , j)) ≡ PN.intoPiece (toℕ i , toℕ j)
    intoPiece-intoPieceℕ _ _ = Fin.toℕ-fromℕ≤ _

    fromPiece-fromPieceℕ : (k : Fin totalSize) → Σ.map toℕ toℕ (fromPiece k) ≡ PN.fromPiece (toℕ k)
    fromPiece-fromPieceℕ k = Σ.≡×≡⇒≡ (Fin.toℕ-fromℕ≤ _ , Fin.toℕ-fromℕ≤ _)

    fromPiece-intoPiece : ∀ {i j} → fromPiece (intoPiece (i , j)) ≡ (i , j)
    fromPiece-intoPiece {i} {j} = Fin.toℕ-injective₂ (begin
      Σ.map toℕ toℕ (fromPiece (intoPiece (i , j)))   ≡⟨ fromPiece-fromPieceℕ _ ⟩
      PN.fromPiece (toℕ (intoPiece (i , j)))          ≡⟨ ≡.cong PN.fromPiece (intoPiece-intoPieceℕ i j) ⟩
      PN.fromPiece (PN.intoPiece (toℕ i , toℕ j))    ≡⟨ PN.fromPiece-intoPiece (Fin.bounded i) (bounded′ j) ⟩
      (toℕ i , toℕ j)                                 ∎)
      where open ≡.Reasoning

    intoPiece-fromPiece : ∀ {k} → intoPiece (fromPiece k) ≡ k
    intoPiece-fromPiece {k} = Fin.toℕ-injective (
      begin
        toℕ (intoPiece (fromPiece k))               ≡⟨ uncurry intoPiece-intoPieceℕ (fromPiece k) ⟩
        PN.intoPiece (Σ.map toℕ toℕ (fromPiece k))  ≡⟨ ≡.cong PN.intoPiece (fromPiece-fromPieceℕ k) ⟩
        PN.intoPiece (PN.fromPiece (toℕ k))         ≡⟨ PN.intoPiece-fromPiece (toℕ k) (Fin.bounded k) ⟩
        toℕ k                                       ∎)
      where open ≡.Reasoning

  asPiece : Σ (Fin numPieces) (Fin ∘ sizeAt) ↔ Fin totalSize
  asPiece = record
    { to = ≡.→-to-⟶ intoPiece
    ; from = ≡.→-to-⟶ fromPiece
    ; inverse-of = record
      { left-inverse-of = λ _ → fromPiece-intoPiece
      ; right-inverse-of = λ _ → intoPiece-fromPiece
      }
    }

Pieces² : ∀ {a} (A : Set a) (size : A → ℕ) → Set a
Pieces² A size = Pieces (Pieces A size) Pieces.totalSize

module _ {a} {A : Set a} {size : A → ℕ} (P₁ : Pieces² A size) where
  private
    module P₁ = Pieces P₁

  module _ (i : Fin P₁.numPieces) where
    private
      P₂ = P₁.pieceAt i
      module P₂ = Pieces P₂

    intoPiece² : (j : Fin P₂.numPieces) → Fin (size (P₂.pieceAt j)) → Fin P₁.totalSize
    intoPiece² j = curry P₁.intoPiece i ∘ curry P₂.intoPiece j

  asPiece² :
    Σ (Fin P₁.numPieces) (λ i →
      let P₂ = P₁.pieceAt i
          module P₂ = Pieces P₂
      in Σ (Fin P₂.numPieces) (Fin ∘ P₂.sizeAt))
    ↔ Fin P₁.totalSize
  asPiece² =
      Σ (Fin P₁.numPieces) (λ i →
        let P₂ = P₁.pieceAt i
            module P₂ = Pieces P₂
        in Σ (Fin P₂.numPieces) (Fin ∘ P₂.sizeAt))
    ↔⟨ Σ-bij (Pieces.asPiece ∘ P₁.pieceAt) ⟩
      Σ (Fin P₁.numPieces) (Fin ∘ P₁.sizeAt)
    ↔⟨ P₁.asPiece ⟩
      Fin P₁.totalSize
    ∎
    where open BijReasoning
