module MLib.Algebra.PropertyCode where

open import MLib.Prelude
open import MLib.Prelude.Fin.Pieces
open import MLib.Prelude.FiniteInj
open import MLib.Algebra.Instances

open import Relation.Binary as B using (Setoid)

open List using (_∷_; [])
open import Data.List.All as All using (All; _∷_; []) public
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

--------------------------------------------------------------------------------
--  Universe of properties
--------------------------------------------------------------------------------

data Property : Set where
  associative commutative idempotent selective cancellative
    leftIdentity rightIdentity
    leftZero rightZero
    distributesOverˡ distributesOverʳ
    : Property

opArities : Property → List ℕ
opArities associative      = 2 ∷ []
opArities commutative      = 2 ∷ []
opArities idempotent       = 2 ∷ []
opArities selective        = 2 ∷ []
opArities cancellative     = 2 ∷ []
opArities leftIdentity     = 0 ∷ 2 ∷ []
opArities rightIdentity    = 0 ∷ 2 ∷ []
opArities leftZero         = 0 ∷ 2 ∷ []
opArities rightZero        = 0 ∷ 2 ∷ []
opArities distributesOverˡ = 2 ∷ 2 ∷ []
opArities distributesOverʳ = 2 ∷ 2 ∷ []

module _ {c ℓ k} {K : ℕ → Set k} (rawStruct : RawStruct c ℓ K) where
  open RawStruct rawStruct
  open Algebra.FunctionProperties _≈_

  interpret : (π : Property) → All K (opArities π) → Set (c ⊔ˡ ℓ)
  interpret associative      (∙ ∷ [])     = Associative ⟦ ∙ ⟧
  interpret commutative      (∙ ∷ [])     = Commutative ⟦ ∙ ⟧
  interpret idempotent       (∙ ∷ [])     = Idempotent ⟦ ∙ ⟧
  interpret selective        (∙ ∷ [])     = Selective ⟦ ∙ ⟧
  interpret cancellative     (∙ ∷ [])     = Cancellative ⟦ ∙ ⟧
  interpret leftIdentity     (ε ∷ ∙ ∷ []) = LeftIdentity ⟦ ε ⟧ ⟦ ∙ ⟧
  interpret rightIdentity    (ε ∷ ∙ ∷ []) = RightIdentity ⟦ ε ⟧ ⟦ ∙ ⟧
  interpret leftZero         (ω ∷ ∙ ∷ []) = LeftZero ⟦ ω ⟧ ⟦ ∙ ⟧
  interpret rightZero        (ω ∷ ∙ ∷ []) = RightZero ⟦ ω ⟧ ⟦ ∙ ⟧
  interpret distributesOverˡ (* ∷ + ∷ []) = ⟦ * ⟧ DistributesOverˡ ⟦ + ⟧
  interpret distributesOverʳ (* ∷ + ∷ []) = ⟦ * ⟧ DistributesOverʳ ⟦ + ⟧

⟦_⟧P : ∀ {c ℓ k} {K : ℕ → Set k} → ∃ (All K ∘ opArities) → RawStruct c ℓ K → Set (c ⊔ˡ ℓ)
⟦ π , ops ⟧P rawStruct = interpret rawStruct π ops

-- TODO: Automate with reflection
allProperties : List Property
allProperties
  = associative
  ∷ commutative
  ∷ idempotent
  ∷ selective
  ∷ cancellative
  ∷ leftIdentity
  ∷ rightIdentity
  ∷ leftZero
  ∷ rightZero
  ∷ distributesOverʳ
  ∷ distributesOverˡ
  ∷ []

--------------------------------------------------------------------------------
--  Subsets of properties over a particular operator code type
--------------------------------------------------------------------------------

record Code k : Set (sucˡ k) where
  field
    K : ℕ → Set k
    boundAt : ℕ → ℕ
    isFiniteAt : ∀ n → IsFiniteSet {A = K n} _≡_ (boundAt n)

  Property′ = ∃ (All K ∘ opArities)

  module _ n where
    open IsFiniteSet (isFiniteAt n) public

  appPropertyToAll : (π : Property) → List (All K (opArities π))
  appPropertyToAll π = All.transpose (All.tabulate {xs = opArities π} (λ {n} _ → enumerate n))

  allAppliedProperties : List Property′
  allAppliedProperties = List.concatMap (λ π → List.map (λ xs → π , xs) (appPropertyToAll π)) allProperties

open Bool

record Properties {k} (code : Code k) : Set k where
  constructor properties

  open Code code

  field
    hasProperty : Property′ → Bool

  HasProperty : Property′ → Set
  HasProperty = T ∘ hasProperty

  hasAll : Bool
  hasAll = List.foldr (λ π b → hasProperty π ∧ b) true allAppliedProperties

  HasAll : Set
  HasAll = T hasAll

open Properties public
open Code using (Property′) public

_∈ₚ_ : ∀ {k} {code : Code k} → Property′ code → Properties code → Set
π ∈ₚ Π = HasProperty Π π

_⇒ₚ_ : ∀ {k} {code : Code k} → Properties code → Properties code → Properties code
hasProperty (Π₁ ⇒ₚ Π₂) π = not (hasProperty Π₁ π) ∨ hasProperty Π₂ π


-- Has⇒ₚ : ∀ {k} {code : Code k} {Π Π′ : Properties code} {π : Property′ code} → π ∈ₚ Π′ → HasAll (Π′ ⇒ₚ Π) → π ∈ₚ Π
-- Has⇒ₚ {Π = Π} {Π′} {π} hasπ hasΠ′ with hasProperty Π π | hasAll
-- Has⇒ₚ hasπ hasΠ′ | h1 | h2 = {!!}

--------------------------------------------------------------------------------
--  Structures with additional properties
--------------------------------------------------------------------------------

record Struct c ℓ {k} {code : Code k} (Π : Properties code) : Set (sucˡ (c ⊔ˡ ℓ ⊔ˡ k)) where
  open Code code hiding (Property′)

  field
    rawStruct : RawStruct c ℓ K
    Π-hold : ∀ {π} → π ∈ₚ Π → ⟦ π ⟧P rawStruct

  open RawStruct rawStruct public

  has : Property′ code → Set
  has π = π ∈ₚ Π

  has′ : Properties code → Set
  has′ Π′ = HasAll (Π ⇒ₚ Π′)

  use : (π : Property′ code) {hasπ : has π} → ⟦ π ⟧P rawStruct
  use π {hasπ} = Π-hold hasπ

  -- from : (Π′ : Properties code) (π : Property′ code) {hasπ : π ∈ₚ Π′} {hasΠ′ : has′ Π′} → ⟦ π ⟧P rawStruct
  -- from Π′ π {hasπ} {hasΠ′} = use π {{!!}}

--------------------------------------------------------------------------------
--  Some named property combinations
--------------------------------------------------------------------------------

private
  Maybe-applicative : ∀ {ℓ} → RawApplicative {ℓ} Maybe
  Maybe-applicative = record
    { pure = just
    ; _⊛_ = maybe Maybe.map λ _ → nothing
    }

subΠ : ∀ {k k′} {code : Code k} {code′ : Code k′} →
  let open Code code using (K)
      open Code code′ using () renaming (K to K′)
  in (∀ {n} → K′ n → Maybe (K n)) →
     Properties code → Properties code′ → Properties code′
hasProperty (subΠ f Π₀ Π₁) π = {!!}

data MagmaK : ℕ → Set where
  ∙ : MagmaK 2

data MonoidK : ℕ → Set where
  ε : MonoidK 0
  ∙ : MonoidK 2

data BimonoidK : ℕ → Set where
  0# 1# : BimonoidK 0
  + * : BimonoidK 2

module _ where
  open Code
  open ℕ

  magmaCode : Code _
  K magmaCode = MagmaK
  boundAt magmaCode 2 = 1
  boundAt magmaCode _ = 0
  isFiniteAt magmaCode 0 = empty-isFinite λ ()
  isFiniteAt magmaCode 1 = empty-isFinite λ ()
  isFiniteAt magmaCode (suc (suc (suc _))) = empty-isFinite λ ()
  isFiniteAt magmaCode 2 = unitary-isFinite (≡.setoid _) ∙ λ {∙ → ≡.refl}

  monoidCode : Code _
  K monoidCode = MonoidK
  boundAt monoidCode 0 = 1
  boundAt monoidCode 2 = 1
  boundAt monoidCode _ = 0
  isFiniteAt monoidCode 0 = unitary-isFinite (≡.setoid _) ε λ {ε → ≡.refl}
  isFiniteAt monoidCode 1 = empty-isFinite λ ()
  isFiniteAt monoidCode 2 = unitary-isFinite (≡.setoid _) ∙ λ {∙ → ≡.refl}
  isFiniteAt monoidCode (suc (suc (suc _))) = empty-isFinite λ ()

--   bimonoidCode : Code _
--   K bimonoidCode = BimonoidK
--   allAtArity bimonoidCode zero = 0# ∷ 1# ∷ []
--   allAtArity bimonoidCode (suc (suc zero)) = + ∷ * ∷ []
--   allAtArity bimonoidCode _ = []

+-part : ∀ {n} → BimonoidK n → Maybe (MonoidK n)
+-part 0# = just ε
+-part + = just ∙
+-part _ = nothing

*-part : ∀ {n} → BimonoidK n → Maybe (MonoidK n)
*-part 1# = just ε
*-part * = just ∙
*-part _ = nothing

isSemigroup : Properties magmaCode
isSemigroup = properties
  λ { (associative , ∙ ∷ []) → true
    ; _ → false}

-- isMonoid : Properties monoidCode
-- isMonoid = subΠ (λ {∙ → just ∙; _ → nothing}) isSemigroup (properties
--   λ { (leftIdentity ε ∙) → true
--     ; (rightIdentity ε ∙) → true
--     ; _ → false
--     })

-- isCommutativeMonoid : Properties monoidCode
-- isCommutativeMonoid = subΠ just isMonoid (properties
--   λ { (commutative ∙) → true
--     ; _ → false
--     })

-- isSemiring : Properties bimonoidCode
-- isSemiring =
--   subΠ +-part isCommutativeMonoid (
--   subΠ *-part isMonoid (properties
--   λ { (leftZero 0# *) → true
--     ; (rightZero 0# *) → true
--     ; (* distributesOverˡ +) → true
--     ; (* distributesOverʳ +) → true
--     ; _ → false
--     }))

-- module Into where
--   open Algebra using (Semigroup; Monoid; CommutativeMonoid)

--   semigroup : ∀ {c ℓ} {Π : Properties magmaCode} ⦃ hasSemigroup : HasAll (Π ⇒ₚ isSemigroup) ⦄ → Struct c ℓ Π → Semigroup c ℓ
--   semigroup struct = record
--     { _∙_ = ⟦ ∙ ⟧
--     ; isSemigroup = record
--       { isEquivalence = isEquivalence
--       ; assoc = {!use (associative ∙)!}
--       ; ∙-cong = {!!}
--       }
--     }
--     where open Struct struct

-- -- -- --   monoid : ∀ {c ℓ} {props} ⦃ _ : isMonoid ⊆ props ⦄ → Dagma props c ℓ → Monoid c ℓ
-- -- -- --   monoid ⦃ mon ⦄ dagma = record
-- -- -- --     { isMonoid = record
-- -- -- --       { isSemigroup = S.isSemigroup
-- -- -- --       ; identity = proj₂ (from isMonoid hasIdentity)
-- -- -- --       }
-- -- -- --     }
-- -- -- --     where
-- -- -- --       open Dagma dagma
-- -- -- --       module S = Semigroup (semigroup (dagma ↓M isMonoid ↓M isSemigroup))

-- -- -- --   commutativeMonoid : ∀ {c ℓ} {props} ⦃ _ : isCommutativeMonoid ⊆ props ⦄ → Dagma props c ℓ → CommutativeMonoid c ℓ
-- -- -- --   commutativeMonoid dagma = record
-- -- -- --     { isCommutativeMonoid = record
-- -- -- --       { isSemigroup = S.isSemigroup
-- -- -- --       ; leftIdentity = proj₁ (proj₂ (from isCommutativeMonoid hasIdentity))
-- -- -- --       ; comm = from isCommutativeMonoid commutative
-- -- -- --       }
-- -- -- --     }
-- -- -- --     where
-- -- -- --       open Dagma dagma
-- -- -- --       module S = Semigroup (semigroup (dagma ↓M isCommutativeMonoid ↓M isSemigroup))

-- -- -- --   -- semiring
