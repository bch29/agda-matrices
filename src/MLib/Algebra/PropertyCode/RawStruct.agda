module MLib.Algebra.PropertyCode.RawStruct where

open import MLib.Prelude
open import MLib.Prelude.Fin.Pieces
open import MLib.Prelude.FiniteInj
open import MLib.Algebra.Instances

open import Relation.Binary as B using (Setoid)

open List using (_∷_; [])
open import Data.List.Any using (Any; here; there)
open import Data.List.Any.Membership.Propositional using (_∈_)

open import Data.Vec using (Vec; _∷_; [])
open import Data.Vec.N-ary
open import Data.Vec.Relation.InductivePointwise using (Pointwise; []; _∷_)

open import Data.Product.Relation.SigmaPropositional as OverΣ using (OverΣ)

open import Data.Bool using (T)

open import Category.Applicative

open import Function.Inverse using (_↔_)
open import Function.LeftInverse using (_↞_; LeftInverse)
open import Function.Equality using (_⟨$⟩_)

-- import Data.Table as Table hiding (module Table)
open Table using (Table)


module _ {c ℓ} {A : Set c} (_≈_ : Rel A ℓ) where
  open Algebra.FunctionProperties _≈_

  Congruentₙ : ∀ {n} → (Vec A n → A) → Set (c ⊔ˡ ℓ)
  Congruentₙ {n} f = ∀ {xs ys} → Pointwise _≈_ xs ys → f xs ≈ f ys

  fromRefl : (∀ {x} → x ≈ x) → (f : Vec A 0 → A) → Congruentₙ f
  fromRefl refl f [] = refl

  fromCongruent₂ : (f : Vec A 2 → A) → Congruent₂ (curryⁿ f) → Congruentₙ f
  fromCongruent₂ f cong₂ (x≈u ∷ y≈v ∷ []) = cong₂ x≈u y≈v

PointwiseFunc : ∀ {n} {a b ℓ r} {A : Set a} {B : Set b} (_∼_ : A → B → Set ℓ) (xs : Vec A n) (ys : Vec B n) (R : Set r) → Set (N-ary-level ℓ r n)
PointwiseFunc _∼_ [] [] R = R
PointwiseFunc _∼_ (x ∷ xs) (y ∷ ys) R = x ∼ y → PointwiseFunc _∼_ xs ys R

appPW : ∀ {n} {a b ℓ r} {A : Set a} {B : Set b} {_∼_ : A → B → Set ℓ} {xs : Vec A n} {ys : Vec B n} {R : Set r} → PointwiseFunc _∼_ xs ys R → Pointwise _∼_ xs ys → R
appPW f [] = f
appPW f (x∼y ∷ pw) = appPW (f x∼y) pw

curryPW : ∀ {n} {a b ℓ r} {A : Set a} {B : Set b} {_∼_ : A → B → Set ℓ} {xs : Vec A n} {ys : Vec B n} {R : Set r} → (Pointwise _∼_ xs ys → R) → PointwiseFunc _∼_ xs ys R
curryPW {xs = []} {[]} f = f []
curryPW {xs = x ∷ xs} {y ∷ ys} f x∼y = curryPW {xs = xs} {ys} λ pw → f (x∼y ∷ pw)

--------------------------------------------------------------------------------
--  Raw structures implementing a set of operators, i.e. interpretations of the
--  operators which are each congruent under an equivalence, but do not
--  necessarily have any other properties.
--------------------------------------------------------------------------------

record IsRawStruct {c ℓ} {A : Set c} (_≈_ : Rel A ℓ) {k} {K : ℕ → Set k} (appOp : ∀ {n} → K n → Vec A n → A) : Set (c ⊔ˡ ℓ ⊔ˡ k) where
  open Algebra.FunctionProperties _≈_
  field
    isEquivalence : IsEquivalence _≈_
    congⁿ : ∀ {n} (κ : K n) → Congruentₙ _≈_ (appOp κ)

  cong : ∀ {n} (κ : K n) {xs ys} → PointwiseFunc _≈_ xs ys (appOp κ xs ≈ appOp κ ys)
  cong κ {xs} = curryPW {xs = xs} (congⁿ κ)

  setoid : Setoid _ _
  setoid = record { isEquivalence = isEquivalence }

  ⟦_⟧ : ∀ {n} → K n → N-ary n A A
  ⟦ κ ⟧ = curryⁿ (appOp κ)

  point : K 0 → A
  point = ⟦_⟧

  _⟨_⟩_ : A → K 2 → A → A
  x ⟨ κ ⟩ y = ⟦ κ ⟧ x y

  open IsEquivalence isEquivalence public

record RawStruct c ℓ {k} (K : ℕ → Set k) : Set (sucˡ (c ⊔ˡ ℓ ⊔ˡ k)) where
  infix 4 _≈_

  field
    Carrier : Set c
    _≈_ : Rel Carrier ℓ
    appOp : ∀ {n} → K n → Vec Carrier n → Carrier
    isRawStruct : IsRawStruct _≈_ appOp

  open IsRawStruct isRawStruct public

  -- If we pick out a subset of the operators in the structure, that too forms a
  -- structure.
  subRawStruct : ∀ {k′} (K′ : ∀ {n} → K n → Set k′) → RawStruct c ℓ (λ n → Σ (K n) K′)
  subRawStruct K′ = record
    { Carrier = Carrier
    ; _≈_ = _≈_
    ; appOp = appOp ∘ proj₁
    ; isRawStruct = record
      { isEquivalence = isEquivalence
      ; congⁿ = congⁿ ∘ proj₁
      }
    }
