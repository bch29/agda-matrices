module MLib.Fin.Pieces.Core where

open import MLib.Prelude

open Nat using (_*_; _+_; _<_)
open Table

sum : ∀ {n} → Table ℕ n → ℕ
sum = foldr _+_ 0

record Pieces {a} (A : Set a) (size : A → ℕ) : Set a where
  field
    numPieces : ℕ
    pieces : Table A numPieces

  pieceAt = lookup pieces
  sizeAt = size ∘ pieceAt
  totalSize = sum (map size pieces)
  pieceSizes = tabulate sizeAt

constPieces : ℕ → ℕ → Pieces ℕ id
constPieces numPieces pieceSize = record
  { numPieces = numPieces
  ; pieces = replicate pieceSize
  }
