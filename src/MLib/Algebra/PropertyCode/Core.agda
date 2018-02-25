module MLib.Algebra.PropertyCode.Core where

open import MLib.Prelude
open import MLib.Prelude.Fin.Pieces
open import MLib.Prelude.Finite
import MLib.Prelude.Finite.Properties as FiniteProps
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
open import Data.Bool.Properties using (∧-isCommutativeMonoid; ∧-idem; T-≡)

open import Category.Applicative

open import Function.Inverse using (_↔_)
open import Function.LeftInverse using (_↞_; LeftInverse)
open import Function.Equality using (_⟨$⟩_)
open import Function.Equivalence using (Equivalence)

open Table using (Table)
open Algebra using (IdempotentCommutativeMonoid)

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


Property-IsFiniteSet : IsFiniteSet Property _
Property-IsFiniteSet = record
  { ontoFin = record
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
finiteProperty = record { isFiniteSetoid = Property-IsFiniteSet }


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
    isFiniteAt : ∀ n → IsFiniteSet (K n) (boundAt n)

  Property′ = Σ Property (All K ∘ opArities)

  module Property′ where
    finiteSet : FiniteSet _ _
    finiteSet = record
      { isFiniteSetoid =
          Σ-isFiniteSet Property-IsFiniteSet (finiteAll boundAt isFiniteAt ∘ opArities)
      }

    open FiniteSet finiteSet public
    open FiniteProps finiteSet public

  allAppliedProperties : List Property′
  allAppliedProperties = FiniteSet.enumerate Property′.finiteSet


open Bool

module BoolExtra where
  ∧-idempotentCommutativeMonoid : IdempotentCommutativeMonoid _ _
  ∧-idempotentCommutativeMonoid = record
    { isIdempotentCommutativeMonoid = record
      { isCommutativeMonoid = ∧-isCommutativeMonoid
      ; idem = ∧-idem
      }
    }

record Properties {k} (code : Code k) : Set k where
  constructor properties

  open Code code

  field
    hasProperty : Property′ → Bool

  record Has (π : Property′) : Set where
    constructor fromTruth
    field
      truth : T (hasProperty π)

  hasAll : Bool
  hasAll = Property′.foldMap BoolExtra.∧-idempotentCommutativeMonoid hasProperty

  -- Inhabited if all the properties are present. Suitable for use as an
  -- implicit argument but difficult to work with.

  record ⊨ : Set where
    constructor fromTruth
    field
      truth : T (hasAll)

  -- Inhabited if all the properties are present. Unsuitable for use as an
  -- implicit argument, but easy to work with.

  ⊢ : Set k
  ⊢ = ∀ π → Has π


open Properties public
open Code using (Property′; module Property′) public

module _ {k} {code : Code k} where

  -- The two forms of truth are equivalent to each other, as we would hope.

  ⊢→⊨ : {Π : Properties code} → ⊢ Π → ⊨ Π
  ⊢→⊨ {Π} p = ⊨.fromTruth (Equivalence.from T-≡ ⟨$⟩ hasAll-true)
    where
    hasProperty-const : ∀ π → hasProperty Π π ≡ true
    hasProperty-const π = Equivalence.to T-≡ ⟨$⟩ Has.truth (p π)

    open ≡.Reasoning
    icm = BoolExtra.∧-idempotentCommutativeMonoid

    hasAll-true : hasAll Π ≡ true
    hasAll-true = begin
      hasAll Π                                        ≡⟨⟩
      Property′.foldMap code icm (hasProperty Π)      ≡⟨ Property′.foldMap-cong code icm hasProperty-const  ⟩
      Property′.foldMap code icm (λ _ → true)         ≡⟨ proj₁ (IdempotentCommutativeMonoid.identity icm) _ ⟩
      true ∧ Property′.foldMap code icm (λ _ → true)  ≡⟨ Property′.foldMap-const code icm ⟩
      true                                            ∎

  ⊨→⊢ : {Π : Properties code} → ⊨ Π → ⊢ Π
  ⊨→⊢ {Π} t π = Has.fromTruth (Equivalence.from T-≡ ⟨$⟩ hasProperty-true)
    where
      i = Property′.toIx code π

      open ≡.Reasoning
      icm = BoolExtra.∧-idempotentCommutativeMonoid
      module ∧ = IdempotentCommutativeMonoid icm

      hasAll-true : hasAll Π ≡ true
      hasAll-true = Equivalence.to T-≡ ⟨$⟩ ⊨.truth t

      hasProperty-true : hasProperty Π π ≡ true
      hasProperty-true = begin
        hasProperty Π π            ≡⟨ ≡.sym (proj₂ ∧.identity _ ) ⟩
        hasProperty Π π ∧ true     ≡⟨ ∧.∙-cong (≡.refl {x = hasProperty Π π}) (≡.sym hasAll-true)  ⟩
        hasProperty Π π ∧ hasAll Π ≡⟨ Property′.enumTable-complete code icm (≡.→-to-⟶ (hasProperty Π)) π ⟩
        hasAll Π                   ≡⟨ hasAll-true ⟩
        true                       ∎

  singleton : Property′ code → Properties code
  singleton π = properties λ π′ → ⌊ Property′._≟_ code π π′ ⌋

  _∈ₚ_ : Property′ code → Properties code → Set
  π ∈ₚ Π = Has Π π

  π-∈ₚ-singleton : ∀ {π} → π ∈ₚ singleton π
  Has.truth (π-∈ₚ-singleton {π}) with Property′._≟_ code π π
  Has.truth (π-∈ₚ-singleton {π}) | yes p = _
  Has.truth (π-∈ₚ-singleton {π}) | no ¬p = ¬p ≡.refl

  _⇒ₚ_ : Properties code → Properties code → Properties code
  hasProperty (Π₁ ⇒ₚ Π₂) π = not (hasProperty Π₁ π) ∨ hasProperty Π₂ π

  Bool-MP : ∀ {x y} → T (not x ∨ y) → T x → T y
  Bool-MP {false} {false} _ ()
  Bool-MP {false} {true} _ _ = tt
  Bool-MP {true} {false} ()
  Bool-MP {true} {true} _ _ = tt

  ⇒ₚ-MP′ : ∀ {Π₁ Π₂} → ⊢ (Π₁ ⇒ₚ Π₂) → ⊢ Π₁ → ⊢ Π₂
  ⇒ₚ-MP′ {Π₁} {Π₂} f g π = Has.fromTruth (Bool-MP (Has.truth (f π)) (Has.truth (g π)))

  ⇒ₚ-MP : ∀ {Π₁ Π₂} → ⊨ (Π₁ ⇒ₚ Π₂) → ⊨ Π₁ → ⊨ Π₂
  ⇒ₚ-MP has⇒ hasΠ₁ = ⊢→⊨ (⇒ₚ-MP′ (⊨→⊢ has⇒) (⊨→⊢ hasΠ₁))

  -- Bool-abs : ∀ {x y} → (T x → T y) → T (not x ∨ y)
  -- Bool-abs {false} {false} f = tt
  -- Bool-abs {false} {true} f = tt
  -- Bool-abs {true} {false} f = f tt
  -- Bool-abs {true} {true} f = tt

  -- ⇒ₚ-abs′ : ∀ {Π₁ Π₂} → (⊢ Π₁ → ⊢ Π₂) → ⊢ (Π₁ ⇒ₚ Π₂)
  -- ⇒ₚ-abs′ f π = fromTruth (Bool-abs {!!})

  -- ⇒ₚ-abs : ∀ {Π₁ Π₂} → (⊨ Π₁ → ⊨ Π₂) → ⊨ (Π₁ ⇒ₚ Π₂)
  -- ⇒ₚ-abs f = ⊢→⊨ (λ π → {!!})

  -- ⇒ₚ-trans : ∀ {Π₁ Π₂ Π₃} → ⊨ (Π₁ ⇒ₚ Π₂) → ⊨ (Π₂ ⇒ₚ Π₃) → ⊨ (Π₁ ⇒ₚ Π₃)
  -- ⇒ₚ-trans {Π₁} p q = ⇒ₚ-abs {Π₁} λ x → ⇒ₚ-MP q (⇒ₚ-MP p x)


  Has⇒ₚ : ∀ {Π Π′ π} → π ∈ₚ Π′ → ⊨ (Π′ ⇒ₚ Π) → π ∈ₚ Π
  Has⇒ₚ {Π = Π} {Π′} {π} hasπ has⇒ =
    fromTruth (Bool-MP (Has.truth (⊨→⊢ has⇒ π)) (Has.truth hasπ))
