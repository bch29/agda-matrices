module MLib.Algebra.PropertyCode where

open import MLib.Prelude
open import MLib.Algebra.Instances

open import Relation.Binary as B using (Setoid)

open List using (_∷_; [])
open import Data.List.All as All using (All; _∷_; []) public
open import Data.List.Any using (Any; here; there)
open import Data.List.Any.Membership.Propositional using (_∈_)

open import Data.Vec using (Vec; _∷_; [])
open import Data.Vec.N-ary
open import Data.Vec.Relation.InductivePointwise using (Pointwise; []; _∷_)


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

--------------------------------------------------------------------------------
--  Universe of properties
--------------------------------------------------------------------------------

data Property {s} (K : ℕ → Set s) : Set s where
  associative commutative idempotent selective cancellative
    : (∙ : K 2) → Property K

  leftIdentity rightIdentity : (ε : K 0) (∙ : K 2) → Property K
  leftZero rightZero : (ω : K 0) (∙ : K 2) → Property K

  _distributesOverˡ_ _distributesOverʳ_ : (* + : K 2) → Property K


module _ {c ℓ k} {K : ℕ → Set k} (rawStruct : RawStruct c ℓ K) where
  open RawStruct rawStruct
  open Algebra.FunctionProperties _≈_

  interpret : Property K → Set (c ⊔ˡ ℓ)
  interpret (associative ∙) = Associative ⟦ ∙ ⟧
  interpret (commutative ∙) = Commutative ⟦ ∙ ⟧
  interpret (idempotent ∙) = Idempotent ⟦ ∙ ⟧
  interpret (selective ∙) = Selective ⟦ ∙ ⟧
  interpret (cancellative ∙) = Cancellative ⟦ ∙ ⟧
  interpret (leftIdentity ε ∙) = LeftIdentity ⟦ ε ⟧ ⟦ ∙ ⟧
  interpret (rightIdentity ε ∙) = RightIdentity ⟦ ε ⟧ ⟦ ∙ ⟧
  interpret (leftZero ω ∙) = LeftZero ⟦ ω ⟧ ⟦ ∙ ⟧
  interpret (rightZero ω ∙) = RightZero ⟦ ω ⟧ ⟦ ∙ ⟧
  interpret (* distributesOverˡ +) = ⟦ * ⟧ DistributesOverˡ ⟦ + ⟧
  interpret (* distributesOverʳ +) = ⟦ * ⟧ DistributesOverʳ ⟦ + ⟧

⟦_⟧P : ∀ {c ℓ k} {K : ℕ → Set k} → Property K → RawStruct c ℓ K → Set (c ⊔ˡ ℓ)
⟦ π ⟧P rawStruct = interpret rawStruct π

--------------------------------------------------------------------------------
--  Structures with additional properties
--------------------------------------------------------------------------------

record Struct c ℓ {k} (K : ℕ → Set k) (Π : List (Property K)) : Set (sucˡ (c ⊔ˡ ℓ ⊔ˡ k)) where
  field
    rawStruct : RawStruct c ℓ K
    properties : All (interpret rawStruct) Π

  open RawStruct rawStruct public

  has : Property K → Set k
  has π = π ∈ Π

  has′ : List (Property K) → Set k
  has′ Π′ = Π′ ⊆ Π

  use : (π : Property K) ⦃ hasπ : has π ⦄ → ⟦ π ⟧P rawStruct
  use π ⦃ hasπ ⦄ = All.lookup properties hasπ

  from : (Π′ : List (Property K)) (π : Property K) ⦃ hasπ : π ∈ Π′ ⦄ ⦃ hasΠ′ : has′ Π′ ⦄ → ⟦ π ⟧P rawStruct
  from _ π ⦃ here ≡.refl ⦄ ⦃ p ∷ hasΠ′ ⦄ = use π ⦃ p ⦄
  from _ _ ⦃ there hasπ ⦄ ⦃ _ ∷ hasΠ′ ⦄ = from _ _ ⦃ hasπ ⦄ ⦃ hasΠ′ ⦄

--------------------------------------------------------------------------------
--  Some named property combinations
--------------------------------------------------------------------------------

-- data MonoidK : ℕ → Set where
  

-- -- isSemigroup : List MagmaProperty
-- -- isSemigroup = associative ∷ []

-- -- isMonoid : List MagmaProperty
-- -- isMonoid = hasIdentity ∷ isSemigroup

-- -- isCommutativeMonoid : List MagmaProperty
-- -- isCommutativeMonoid = commutative ∷ isMonoid

-- -- isSemiring : List BimagmaProperty
-- -- isSemiring
-- --   =  map on+ isCommutativeMonoid
-- --   ++ map on* isMonoid
-- --   ++ leftDistributive
-- --    ∷ rightDistributive
-- --    ∷ on* hasZero
-- --    ∷ []
-- --   where open List

-- -- module Into where
-- --   open Algebra using (Semigroup; Monoid; CommutativeMonoid)

-- --   infixl 0 _↓M_

-- --   _↓M_ : ∀ {c ℓ} {strongProps} → Dagma strongProps c ℓ → ∀ weakProps ⦃ sub : weakProps ⊆ strongProps ⦄ → Dagma weakProps c ℓ
-- --   _↓M_ dagma _ ⦃ sub ⦄ = record
-- --     { magma = magma
-- --     ; properties = getAll⊆ sub properties
-- --     }
-- --     where open Dagma dagma

-- --   _↓B_ : ∀ {c ℓ} {strongProps} → Bidagma strongProps c ℓ → ∀ weakProps ⦃ sub : weakProps ⊆ strongProps ⦄ → Bidagma weakProps c ℓ
-- --   _↓B_ bidagma _ ⦃ sub ⦄ = record
-- --     { bimagma = bimagma
-- --     ; properties = getAll⊆ sub properties
-- --     }
-- --     where open Bidagma bidagma

-- --   semigroup : ∀ {c ℓ} {props} ⦃ _ : isSemigroup ⊆ props ⦄ → Dagma props c ℓ → Semigroup c ℓ
-- --   semigroup dagma = record
-- --     { isSemigroup = record
-- --       { isEquivalence = isEquivalence
-- --       ; assoc = from isSemigroup associative
-- --       ; ∙-cong = ∙-cong
-- --       }
-- --     }
-- --     where open Dagma dagma

-- --   monoid : ∀ {c ℓ} {props} ⦃ _ : isMonoid ⊆ props ⦄ → Dagma props c ℓ → Monoid c ℓ
-- --   monoid ⦃ mon ⦄ dagma = record
-- --     { isMonoid = record
-- --       { isSemigroup = S.isSemigroup
-- --       ; identity = proj₂ (from isMonoid hasIdentity)
-- --       }
-- --     }
-- --     where
-- --       open Dagma dagma
-- --       module S = Semigroup (semigroup (dagma ↓M isMonoid ↓M isSemigroup))

-- --   commutativeMonoid : ∀ {c ℓ} {props} ⦃ _ : isCommutativeMonoid ⊆ props ⦄ → Dagma props c ℓ → CommutativeMonoid c ℓ
-- --   commutativeMonoid dagma = record
-- --     { isCommutativeMonoid = record
-- --       { isSemigroup = S.isSemigroup
-- --       ; leftIdentity = proj₁ (proj₂ (from isCommutativeMonoid hasIdentity))
-- --       ; comm = from isCommutativeMonoid commutative
-- --       }
-- --     }
-- --     where
-- --       open Dagma dagma
-- --       module S = Semigroup (semigroup (dagma ↓M isCommutativeMonoid ↓M isSemigroup))

-- --   -- semiring
