open import MLib.Algebra.PropertyCode
open import MLib.Algebra.PropertyCode.Structures

module MLib.Matrix {c ℓ} (struct : Struct bimonoidCode c ℓ) where

open import MLib.Prelude
open import MLib.Matrix.Core
open import MLib.Algebra.Operations struct

open Algebra using (CommutativeMonoid)
open PropertyC
open Table using (head; tail; rearrange; fromList; toList; _≗_)

open OverBimonoid struct
open import MLib.Matrix.Plus struct
open import MLib.Matrix.Mul struct
open FunctionProperties
