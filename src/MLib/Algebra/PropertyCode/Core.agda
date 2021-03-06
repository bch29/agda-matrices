module MLib.Algebra.PropertyCode.Core where

open import MLib.Prelude
open import MLib.Finite
import MLib.Finite.Properties as FiniteProps
open import MLib.Algebra.PropertyCode.RawStruct

import Relation.Unary as U using (Decidable)
open import Relation.Binary as B using (Setoid)

open List.All using (All; _∷_; [])
open import Data.List.Any using (Any; here; there)
open import Data.List.Membership.Propositional using (_∈_)

open import Data.Vec.N-ary

open import Data.Product.Relation.SigmaPropositional as OverΣ using (OverΣ)

open import Data.Bool using (T)

open import Category.Applicative

open LeftInverse using () renaming (_∘_ to _∘ⁱ_)
open FE using (_⇨_; cong)
open import Function.Equivalence using (Equivalence)

open Table using (Table)
open Algebra using (IdempotentCommutativeMonoid)

--------------------------------------------------------------------------------
--  Extra theorems about bools
--------------------------------------------------------------------------------

open Bool

module BoolExtra where
  _⇒_ : Bool → Bool → Bool
  false ⇒ false = true
  false ⇒ true = true
  true ⇒ false = false
  true ⇒ true = true

  true⇒ : ∀ {x} → true ⇒ x ≡ x
  true⇒ {false} = ≡.refl
  true⇒ {true} = ≡.refl

  MP : ∀ {x y} → T (x ⇒ y) → T x → T y
  MP {false} {false} _ ()
  MP {false} {true} _ _ = tt
  MP {true} {false} ()
  MP {true} {true} _ _ = tt

  abs : ∀ {x y} → (T x → T y) → T (x ⇒ y)
  abs {false} {false} f = tt
  abs {false} {true} f = tt
  abs {true} {false} f = f tt
  abs {true} {true} f = tt

  ∧-elim : ∀ {x y} → T (x ∧ y) → T x × T y
  ∧-elim {false} {false} ()
  ∧-elim {false} {true} ()
  ∧-elim {true} {false} ()
  ∧-elim {true} {true} p = tt , tt

--------------------------------------------------------------------------------
--  Universe of properties
--------------------------------------------------------------------------------

data PropKind : Set where
  associative commutative idempotent selective cancellative
    leftIdentity rightIdentity
    leftZero rightZero
    distributesOverˡ distributesOverʳ
    : PropKind


opArities : PropKind → List ℕ
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


module _ {c ℓ k} {K : ℕ → Set k} (rawStruct : RawStruct K c ℓ) where
  open RawStruct rawStruct
  open Algebra.FunctionProperties _≈_

  interpret : (π : PropKind) → All K (opArities π) → Set (c ⊔ˡ ℓ)
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

Property : ∀ {k} (K : ℕ → Set k) → Set k
Property K = ∃ (All K ∘ opArities)

module PropertyC where
  natsEqual : ℕ → ℕ → Bool
  natsEqual Nat.zero Nat.zero = true
  natsEqual Nat.zero (Nat.suc y) = false
  natsEqual (Nat.suc x) Nat.zero = false
  natsEqual (Nat.suc x) (Nat.suc y) = natsEqual x y

  aritiesMatch : List ℕ → List ℕ → Bool
  aritiesMatch [] [] = true
  aritiesMatch [] (x ∷ ys) = false
  aritiesMatch (x ∷ xs) [] = false
  aritiesMatch (x ∷ xs) (y ∷ ys) = natsEqual x y ∧ aritiesMatch xs ys

  natsEqual-correct : ∀ {m n} → T (natsEqual m n) → m ≡ n
  natsEqual-correct {Nat.zero} {Nat.zero} p = ≡.refl
  natsEqual-correct {Nat.zero} {Nat.suc n} ()
  natsEqual-correct {Nat.suc m} {Nat.zero} ()
  natsEqual-correct {Nat.suc m} {Nat.suc n} p = ≡.cong Nat.suc (natsEqual-correct p)

  aritiesMatch-correct : ∀ {xs ys} → T (aritiesMatch xs ys) → xs ≡ ys
  aritiesMatch-correct {[]} {[]} p = ≡.refl
  aritiesMatch-correct {[]} {x ∷ ys} ()
  aritiesMatch-correct {x ∷ xs} {[]} ()
  aritiesMatch-correct {x ∷ xs} {y ∷ ys} p =
    let q , r = BoolExtra.∧-elim {natsEqual x y} p
    in ≡.cong₂ _∷_ (natsEqual-correct q) (aritiesMatch-correct r)

  _on_ : ∀ {k} {K : ℕ → Set k} {n : ℕ} (π : PropKind) {_ : T (aritiesMatch (opArities π) (n ∷ []))} → K n → Property K
  _on_ {K = K} π {match} κ = π , ≡.subst (All K) (≡.sym (aritiesMatch-correct {opArities π} match)) (κ ∷ [])

  _is_for_ : ∀ {k} {K : ℕ → Set k} {m n : ℕ} → K m → (π : PropKind) {_ : T (aritiesMatch (opArities π) (m ∷ n ∷ []))} → K n → Property K
  _is_for_ {K = K} α π {match} ∙ = π , ≡.subst (All K) (≡.sym (aritiesMatch-correct {opArities π} match)) (α ∷ ∙ ∷ [])

  _⟨_⟩ₚ_ = _is_for_

⟦_⟧P : ∀ {c ℓ k} {K : ℕ → Set k} → Property K → RawStruct K c ℓ → Set (c ⊔ˡ ℓ)
⟦ π , ops ⟧P rawStruct = interpret rawStruct π ops


PropKind-IsFiniteSet : IsFiniteSet PropKind _
PropKind-IsFiniteSet = record
  { ontoFin = record
    { to = ≡.→-to-⟶ to
    ; from = ≡.→-to-⟶ from
    ; left-inverse-of = left-inverse-of
    }
  }
  where
    open Fin using (#_) renaming (zero to z; suc to s_)

    N = 11

    to : PropKind → Fin N
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

    from : Fin N → PropKind
    from z                       = associative
    from (s z)                   = commutative
    from (s s z)                 = idempotent
    from (s s s z)               = selective
    from (s s s s z)             = cancellative
    from (s s s s s z)           = leftIdentity
    from (s s s s s s z)         = rightIdentity
    from (s s s s s s s z)       = leftZero
    from (s s s s s s s s z)     = rightZero
    from (s s s s s s s s s z)   = distributesOverˡ
    from (s s s s s s s s s s z) = distributesOverʳ
    from (s s s s s s s s s s s ())

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


finitePropKind : FiniteSet _ _
finitePropKind = record { isFiniteSetoid = PropKind-IsFiniteSet }


--------------------------------------------------------------------------------
--  Subsets of properties over a particular operator code type
--------------------------------------------------------------------------------

record Code k : Set (sucˡ k) where
  field
    K : ℕ → Set k
    boundAt : ℕ → ℕ
    isFiniteAt : ∀ n → IsFiniteSet (K n) (boundAt n)

  finiteSetAt : ℕ → FiniteSet _ _
  finiteSetAt n = record { isFiniteSetoid = isFiniteAt n }

  module K n = FiniteSet (finiteSetAt n)

  module Property where
    finiteSet : FiniteSet _ _
    finiteSet = record
      { isFiniteSetoid =
          Σ-isFiniteSetoid PropKind-IsFiniteSet (All-finiteSet finiteSetAt ∘ opArities)
      }

    open FiniteSet finiteSet public
    open FiniteProps finiteSet public

    ≈⇒≡ : ∀ {π π′} → π ≈ π′ → π ≡ π′
    ≈⇒≡ {π , κ} {.π , κ′} (≡.refl , snd) with All′.PW-≡ _ snd
    ≈⇒≡ {π , κ} {.π , .κ} (≡.refl , snd) | ≡.refl = ≡.refl


record IsSubcode {k k′} (sub : Code k) (sup : Code k′) : Set (k ⊔ˡ k′) where
  constructor subcode

  private
    module Sub = Code sub
    module Sup = Code sup

  field
    subK→supK : ∀ {n} → Sub.K n → Sup.K n
    supK→subK : ∀ {n} → Sup.K n → Maybe (Sub.K n)
    acrossSub : ∀ {n} (κ : Sub.K n) → supK→subK (subK→supK κ) ≡ just κ

mapProperty :
  ∀ {k k′} {K : ℕ → Set k} {K′ : ℕ → Set k′}
  → (∀ {n} → K′ n → K n)
  → Property K′
  → Property K
mapProperty f (π , κs) = π , List.All.map f κs

record Properties {k} (code : Code k) : Set k where
  constructor properties

  open Code code using (K; module Property)

  field
    hasProperty : Property K → Bool

  hasPropertyF : Property.setoid ⟶ ≡.setoid Bool
  _⟨$⟩_ hasPropertyF = hasProperty
  cong hasPropertyF (≡.refl , q) rewrite All′.PW-≡ K q = ≡.refl

open Properties public

module _ {k} {code : Code k} where
  open Code code using (K; module Property)

  Property-Func : Setoid _ _
  Property-Func = Property.setoid ⇨ ≡.setoid Bool

  Properties-setoid : Setoid _ _
  Properties-setoid = record
    { Carrier = Properties code
    ; _≈_ = λ Π Π′ → hasPropertyF Π ≈ hasPropertyF Π′
    ; isEquivalence = record
      { refl = λ {Π} → refl {hasPropertyF Π}
      ; sym = λ {Π} {Π′} → sym {hasPropertyF Π} {hasPropertyF Π′}
      ; trans = λ {Π} {Π′} {Π′′} → trans {hasPropertyF Π} {hasPropertyF Π′} {hasPropertyF Π′′}
      }
    }
    where
    open Setoid Property-Func

  Properties↞Func : LeftInverse Properties-setoid Property-Func
  Properties↞Func = record
    { to = record { _⟨$⟩_ = hasPropertyF ; cong = id }
    ; from = record { _⟨$⟩_ = properties ∘ _⟨$⟩_ ; cong = id }
    ; left-inverse-of = left-inverse-of
    }
    where
    open Setoid Property.setoid using (_≈_)
    left-inverse-of : ∀ (Π : Properties code) {π π′} → π ≈ π′ → hasProperty Π π ≡ hasProperty Π π′
    left-inverse-of Π (≡.refl , p) rewrite All′.PW-≡ K p = ≡.refl

  -- Properties↞ℕ : LeftInverse Properties-setoid (≡.setoid ℕ)
  -- Properties↞ℕ = asNat Property.finiteSet ∘ⁱ Properties↞Func

  -- Evaluates to 'true' only when every property is present.

  hasAll : Properties code → Bool
  hasAll Π = Property.foldMap Bool.∧-idempotentCommutativeMonoid (hasProperty Π)

  implies : Properties code → Properties code → Bool
  implies Π₁ Π₂ = Property.foldMap Bool.∧-idempotentCommutativeMonoid (λ π → hasProperty Π₁ π BoolExtra.⇒ hasProperty Π₂ π)

  -- The full set of properties

  True : Properties code
  hasProperty True _ = true

  -- The empty set of properties

  False : Properties code
  hasProperty False _ = false


  -- Inhabited if the given property is present. Suitable for use as an instance
  -- argument.

  record _∈ₚ_ (π : Property K) (Π : Properties code) : Set where
    instance constructor fromTruth
    field
      truth : T (hasProperty Π π)

  open _∈ₚ_

  -- Inhabited if the first set of properties implies the second. Suitable for
  -- use as an instance argument but difficult to work with.

  record _⇒ₚ_ (Π₁ Π₂ : Properties code) : Set where
    instance constructor fromTruth
    field
      truth : T (implies Π₁ Π₂)

  ⊨ : Properties code → Set
  ⊨ Π = True ⇒ₚ Π


  -- Inhabited if the first set of properties implies the second. Unsuitable for
  -- use as an instance argument, but easy to work with.

  _→ₚ_ : Properties code → Properties code → Set k
  Π₁ →ₚ Π₂ = ∀ π → π ∈ₚ Π₁ → π ∈ₚ Π₂

  ⊢ : Properties code → Set k
  ⊢ Π = True →ₚ Π

  -- The two forms of implication are equivalent to each other, as we would hope

  →ₚ-⇒ₚ : {Π₁ Π₂ : Properties code} → Π₁ →ₚ Π₂ → Π₁ ⇒ₚ Π₂
  →ₚ-⇒ₚ {Π₁} {Π₂} p = _⇒ₚ_.fromTruth (Equivalence.from T-≡ ⟨$⟩ impl-true)
    where
    open ≡.Reasoning

    icm = Bool.∧-idempotentCommutativeMonoid

    impl-pointwise : ∀ π → hasProperty Π₁ π BoolExtra.⇒ hasProperty Π₂ π ≡ true
    impl-pointwise π = Equivalence.to T-≡ ⟨$⟩ BoolExtra.abs (truth ∘ p π ∘ fromTruth)

    impl-true : implies Π₁ Π₂ ≡ true
    impl-true = begin
      implies Π₁ Π₂                 ≡⟨⟩
      Property.foldMap icm (λ π → hasProperty Π₁ π BoolExtra.⇒ hasProperty Π₂ π) ≡⟨ Property.foldMap-cong icm impl-pointwise ⟩
      Property.foldMap icm (λ _ → true) ≡⟨ proj₁ (IdempotentCommutativeMonoid.identity icm) _ ⟩
      true ∧ Property.foldMap icm (λ _ → true) ≡⟨ Property.foldMap-const icm ⟩
      true ∎

  ⇒ₚ-→ₚ : {Π₁ Π₂ : Properties code} → Π₁ ⇒ₚ Π₂ → Π₁ →ₚ Π₂
  ⇒ₚ-→ₚ {Π₁} {Π₂} (fromTruth p) π (fromTruth q) = fromTruth (BoolExtra.MP (Equivalence.from T-≡ ⟨$⟩ impl-π) q)
    where
      i = Property.toIx π

      open ≡.Reasoning
      icm = Bool.∧-idempotentCommutativeMonoid
      module ∧ = IdempotentCommutativeMonoid icm

      implies-true : implies Π₁ Π₂ ≡ true
      implies-true = Equivalence.to T-≡ ⟨$⟩ p

      implies-F : Property.setoid ⟶ ≡.setoid Bool
      implies-F = record
        { _⟨$⟩_ = λ π → hasProperty Π₁ π BoolExtra.⇒ hasProperty Π₂ π
        ; cong = λ { {π} {π′} p → ≡.cong₂ BoolExtra._⇒_ (cong (hasPropertyF Π₁) p) (cong (hasPropertyF Π₂) p)}
        }

      impl-π : hasProperty Π₁ π BoolExtra.⇒ hasProperty Π₂ π ≡ true
      impl-π = begin
        hasProperty Π₁ π BoolExtra.⇒ hasProperty Π₂ π                     ≡⟨ ≡.sym (proj₂ ∧.identity _) ⟩
        (hasProperty Π₁ π BoolExtra.⇒ hasProperty Π₂ π) ∧ true            ≡⟨ ∧.∙-cong (≡.refl {x = hasProperty Π₁ π BoolExtra.⇒ hasProperty Π₂ π}) (≡.sym implies-true) ⟩
        (hasProperty Π₁ π BoolExtra.⇒ hasProperty Π₂ π) ∧ implies Π₁ Π₂   ≡⟨ Property.enumₜ-complete icm implies-F π ⟩
        implies Π₁ Π₂                                                     ≡⟨ implies-true ⟩
        true ∎

  -- Form a set of properties from a single property

  singleton : Property K → Properties code
  hasProperty (singleton π) π′ = ⌊ π Property.≟ π′ ⌋

  -- Union of two sets of properties

  _∪ₚ_ : Properties code → Properties code → Properties code
  hasProperty (Π₁ ∪ₚ Π₂) π = hasProperty Π₁ π ∨ hasProperty Π₂ π

  -- Form a set of properties from a list of properties

  fromList : List (Property K) → Properties code
  fromList = List.foldr (_∪ₚ_ ∘ singleton) False

  π-∈ₚ-singleton : ∀ {π} → π ∈ₚ singleton π
  truth (π-∈ₚ-singleton {π}) with π Property.≟ π
  truth (π-∈ₚ-singleton {π}) | yes p = _
  truth (π-∈ₚ-singleton {π}) | no ¬p = ¬p Property.refl

  _⊆_ : Properties code → Properties code → Properties code
  hasProperty (Π₁ ⊆ Π₂) π = not (hasProperty Π₁ π) ∨ hasProperty Π₂ π

  →ₚ-trans : ∀ {Π₁ Π₂ Π₃} → Π₁ →ₚ Π₂ → Π₂ →ₚ Π₃ → Π₁ →ₚ Π₃
  →ₚ-trans {Π₁} p q π = q π ∘ p π

  ⇒ₚ-trans : ∀ {Π₁ Π₂ Π₃} → Π₁ ⇒ₚ Π₂ → Π₂ ⇒ₚ Π₃ → Π₁ ⇒ₚ Π₃
  ⇒ₚ-trans {Π₁} p q = →ₚ-⇒ₚ (→ₚ-trans (⇒ₚ-→ₚ p) (⇒ₚ-→ₚ q))

  ⇒ₚ-MP : ∀ {Π Π′ π} → π ∈ₚ Π′ → Π′ ⇒ₚ Π → π ∈ₚ Π
  ⇒ₚ-MP {Π = Π} {Π′} {π} hasπ has⇒ = ⇒ₚ-→ₚ has⇒ π hasπ

  ⇒ₚ-weaken : ∀ {Π Π′ Π′′ : Properties code} (hasΠ′ : Π′ ⇒ₚ Π) ⦃ hasΠ′′ : Π′′ ⇒ₚ Π′ ⦄ → Π′′ ⇒ₚ Π
  ⇒ₚ-weaken hasΠ′ ⦃ hasΠ′′ ⦄ = ⇒ₚ-trans hasΠ′′ hasΠ′

module _ {k k′} {sub : Code k} {sup : Code k′} (isSub : IsSubcode sub sup) where
  private
    module Sub = Code sub
    module Sup = Code sup

  open IsSubcode isSub public

  subcodeProperties : Properties sup → Properties sub
  hasProperty (subcodeProperties Π) = hasProperty Π ∘ mapProperty subK→supK

  supcodeProperties : Properties sub → Properties sup
  hasProperty (supcodeProperties Π) (π , κs) with List.All.traverse supK→subK κs
  hasProperty (supcodeProperties Π) (π , κs) | just κs′ = hasProperty Π (π , κs′)
  hasProperty (supcodeProperties Π) (π , κs) | nothing = false

  fromSubcode :
    ∀ {π} {Π : Properties sup}
    → π ∈ₚ subcodeProperties Π
    → mapProperty subK→supK π ∈ₚ Π
  fromSubcode (fromTruth truth) = fromTruth truth

  fromSupcode :
    ∀ {π} {Π : Properties sup}
    → mapProperty subK→supK π ∈ₚ Π
    → π ∈ₚ subcodeProperties Π
  fromSupcode (fromTruth truth) = fromTruth truth

  fromSupcode′ : ∀ {π} {Π : Properties sub} →
    π ∈ₚ Π → mapProperty subK→supK π ∈ₚ supcodeProperties Π
  fromSupcode′ {π , κs} π∈Π ._∈ₚ_.truth with lem
    where
    open ≡.Reasoning
    lem : List.All.traverse supK→subK (List.All.map subK→supK κs) ≡ just κs
    lem = begin
      List.All.traverse supK→subK (List.All.map subK→supK κs) ≡⟨ List-All.traverse-map supK→subK subK→supK κs ⟩
      List.All.traverse (supK→subK ∘ subK→supK) κs ≡⟨ List-All.traverse-cong (supK→subK ∘ subK→supK) just acrossSub κs ⟩
      List.All.traverse just κs ≡⟨ List-All.traverse-just κs ⟩
      just κs ∎
  fromSupcode′ {π , κs} π∈Π ._∈ₚ_.truth | p rewrite p = π∈Π ._∈ₚ_.truth


  module _
    {c ℓ}
    (sup-rawStruct : RawStruct Sup.K c ℓ)
    (sub-isRawStruct : IsRawStruct (RawStruct._≈_ sup-rawStruct) (RawStruct.appOp sup-rawStruct ∘ subK→supK)) where

    sub-rawStruct : RawStruct Sub.K c ℓ
    sub-rawStruct = record { isRawStruct = sub-isRawStruct }

    reinterpret :
      ∀ (π : Property Sub.K)
      → ⟦ mapProperty subK→supK π ⟧P sup-rawStruct → ⟦ π ⟧P sub-rawStruct
    reinterpret (associative      , ∙ ∷ [])     = id
    reinterpret (commutative      , ∙ ∷ [])     = id
    reinterpret (idempotent       , ∙ ∷ [])     = id
    reinterpret (selective        , ∙ ∷ [])     = id
    reinterpret (cancellative     , ∙ ∷ [])     = id
    reinterpret (leftIdentity     , α ∷ ∙ ∷ []) = id
    reinterpret (rightIdentity    , α ∷ ∙ ∷ []) = id
    reinterpret (leftZero         , α ∷ ∙ ∷ []) = id
    reinterpret (rightZero        , α ∷ ∙ ∷ []) = id
    reinterpret (distributesOverˡ , * ∷ + ∷ []) = id
    reinterpret (distributesOverʳ , * ∷ + ∷ []) = id
