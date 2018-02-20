module MLib.Algebra.PropertyCode.Core where

open import MLib.Prelude
open import MLib.Prelude.Fin.Pieces
open import MLib.Prelude.FiniteInj
open import MLib.Algebra.PropertyCode.RawStruct
open import MLib.Algebra.Instances

open import Relation.Binary as B using (Setoid)

open List using (_∷_; [])
open import Data.List.All as All using (All; _∷_; [])
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

open Table using (Table)


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


Property-IsFiniteSet : IsFiniteSet {A = Property} _≡_ _
Property-IsFiniteSet = record
  { isEquivalence = ≡.isEquivalence
  ; ontoFin = record
    { to = ≡.→-to-⟶ to
    ; from = ≡.→-to-⟶ from
    ; left-inverse-of = left-inverse-of
    }
  }
  where
    open Fin using (#_) renaming (zero to z; suc to s)

    N = 11

    to : Property → Fin N
    to associative      = # 0
    to commutative      = # 1
    to idempotent       = # 2
    to selective        = # 3
    to cancellative     = # 4
    to leftIdentity     = # 5
    to rightIdentity    = # 6
    to leftZero         = # 7
    to rightZero        = # 8
    to distributesOverˡ = # 9
    to distributesOverʳ = # 10

    from : Fin N → Property
    from z                                         = associative
    from (s z)                                     = commutative
    from (s (s z))                                 = idempotent
    from (s (s (s z)))                             = selective
    from (s (s (s (s z))))                         = cancellative
    from (s (s (s (s (s z)))))                     = leftIdentity
    from (s (s (s (s (s (s z))))))                 = rightIdentity
    from (s (s (s (s (s (s (s z)))))))             = leftZero
    from (s (s (s (s (s (s (s (s z))))))))         = rightZero
    from (s (s (s (s (s (s (s (s (s z)))))))))     = distributesOverˡ
    from (s (s (s (s (s (s (s (s (s (s z)))))))))) = distributesOverʳ
    from (s (s (s (s (s (s (s (s (s (s (s ())))))))))))

    left-inverse-of : ∀ x → from (to x) ≡ x
    left-inverse-of associative      = ≡.refl
    left-inverse-of commutative      = ≡.refl
    left-inverse-of idempotent       = ≡.refl
    left-inverse-of selective        = ≡.refl
    left-inverse-of cancellative     = ≡.refl
    left-inverse-of leftIdentity     = ≡.refl
    left-inverse-of rightIdentity    = ≡.refl
    left-inverse-of leftZero         = ≡.refl
    left-inverse-of rightZero        = ≡.refl
    left-inverse-of distributesOverˡ = ≡.refl
    left-inverse-of distributesOverʳ = ≡.refl


finiteProperty : FiniteSet _ _
finiteProperty = record { isFiniteSet = Property-IsFiniteSet }


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

  Property′ = Σₜ finiteProperty (All K ∘ opArities)

  Property′-IsFiniteSet : IsFiniteSet {A = Property′} _≡_ _
  Property′-IsFiniteSet =
    Σₜ-isFiniteSet Property-IsFiniteSet (λ {x} → finiteAll {P = K} {boundAt} (isFiniteAt _) {opArities x})

  allAppliedProperties : List Property′
  allAppliedProperties = IsFiniteSet.enumerate Property′-IsFiniteSet


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


Has⇒ₚ : ∀ {k} {code : Code k} {Π Π′ : Properties code} {π : Property′ code} → π ∈ₚ Π′ → HasAll (Π′ ⇒ₚ Π) → π ∈ₚ Π
Has⇒ₚ {Π = Π} {Π′} {π} hasπ hasΠ′ = {!!}

