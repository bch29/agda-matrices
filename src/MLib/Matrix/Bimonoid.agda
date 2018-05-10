open import MLib.Algebra.PropertyCode
open import MLib.Algebra.PropertyCode.Structures

module MLib.Matrix.Bimonoid {c ℓ} (struct : Struct bimonoidCode c ℓ) where

open import MLib.Prelude
open import MLib.Matrix.Core
open import MLib.Matrix.Equality struct
open import MLib.Matrix.Mul struct
open import MLib.Matrix.Plus struct
open import MLib.Algebra.Operations struct
open import MLib.Algebra.PropertyCode.Dependent struct

open FunctionProperties

matrixRawStruct : ∀ n → RawStruct BimonoidK _ _
matrixRawStruct n = record
  { appOp = λ
    { + (A ∷ B ∷ []) → A ⊕ B
    ; * (A ∷ B ∷ []) → A ⊗ B
    ; 0# [] → 0●
    ; 1# [] → 1●
    }
  ; isRawStruct = record
    { isEquivalence = isEquivalence {n} {n}
    ; congⁿ = λ
      { + (p ∷ q ∷ []) i j → cong + (p i j) (q i j)
      ; * (p ∷ q ∷ []) → ⊗-cong p q
      ; 0# [] _ _ → S.refl
      ; 1# [] _ _ → S.refl
      }
    }
  }

matrixStruct : ∀ n → Struct bimonoidCode _ _
matrixStruct n = dependentStruct (matrixRawStruct n)
  ( (commutative on + , _ , ⊕-comm)
  ∷ (associative on + , _ , ⊕-assoc)
  ∷ (0# is leftIdentity for + , _ , ⊕-identityˡ)
  ∷ (0# is rightIdentity for + , _ , ⊕-identityʳ)
  ∷ (associative on * , _ , ⊗-assoc)
  ∷ (* ⟨ distributesOverˡ ⟩ₚ + , _ , ⊗-distributesOverˡ-⊕)
  ∷ [])
