module MLib.Matrix.Core where

open import MLib.Prelude
open import MLib.Algebra.PropertyCode
open import MLib.Algebra.PropertyCode.Structures

import Relation.Binary.Indexed as I

Matrix : ∀ {a} → Set a → ℕ → ℕ → Set a
Matrix A m n = Fin m → Fin n → A

module _ {a} (A : Set a) where
  row : ∀ {m n} → Fin m → Matrix A m n → Table A n
  row i M .lookup j = M i j

  col : ∀ {m n} → Fin n → Matrix A m n → Table A m
  col j M .lookup i = M i j
