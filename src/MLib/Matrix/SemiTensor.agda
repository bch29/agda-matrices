open import MLib.Algebra.PropertyCode
open import MLib.Algebra.PropertyCode.Structures

module MLib.Matrix.SemiTensor {c ℓ} (struct : Struct bimonoidCode c ℓ) where

open import MLib.Matrix.SemiTensor.Core struct using (_⋉_) public
open import MLib.Matrix.SemiTensor.GeneralizesMul struct public
