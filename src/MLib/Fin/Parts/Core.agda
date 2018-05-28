module MLib.Fin.Parts.Core where

open import MLib.Prelude

open Nat using (_*_; _+_; _<_)
open Table

record Parts {a} (A : Set a) (size : A → ℕ) : Set a where
  field
    numParts : ℕ
    parts : Table A numParts

  partAt = lookup parts
  sizeAt = size ∘ partAt
  totalSize = sum (map size parts)
  partsizes = tabulate sizeAt

constParts : ℕ → ℕ → Parts ℕ id
constParts numParts partsize = record
  { numParts = numParts
  ; parts = replicate partsize
  }
