open import MLib.Algebra.PropertyCode
open import MLib.Algebra.PropertyCode.Structures

module MLib.Matrix {c ℓ} (struct : Struct bimonoidCode c ℓ) where

open import MLib.Prelude
open Struct struct
open import MLib.Algebra.Operations struct

open Table using (head; tail; rearrange; fromList; toList; _≗_)

open import MLib.Matrix.Core public
open import MLib.Matrix.Equality struct public
open import MLib.Matrix.Plus struct public
open import MLib.Matrix.Mul struct public
open import MLib.Matrix.Tensor struct public
open import MLib.Matrix.SemiTensor struct public
open FunctionProperties
