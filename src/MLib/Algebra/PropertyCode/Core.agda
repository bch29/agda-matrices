module MLib.Algebra.PropertyCode.Core where

open import MLib.Prelude
open import MLib.Prelude.Fin.Pieces
open import MLib.Prelude.Finite
import MLib.Prelude.Finite.Properties as FiniteProps
open import MLib.Algebra.PropertyCode.RawStruct
open import MLib.Algebra.Instances

import Relation.Unary as U using (Decidable)
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
--  Extra theorems about bools
--------------------------------------------------------------------------------

open Bool

module BoolExtra where
  ∧-idempotentCommutativeMonoid : IdempotentCommutativeMonoid _ _
  ∧-idempotentCommutativeMonoid = record
    { isIdempotentCommutativeMonoid = record
      { isCommutativeMonoid = ∧-isCommutativeMonoid
      ; idem = ∧-idem
      }
    }

  MP : ∀ {x y} → T (not x ∨ y) → T x → T y
  MP {false} {false} _ ()
  MP {false} {true} _ _ = tt
  MP {true} {false} ()
  MP {true} {true} _ _ = tt

  abs : ∀ {x y} → (T x → T y) → T (not x ∨ y)
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
    open Fin using (#_) renaming (zero to z; suc to s)

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


finitePropKind : FiniteSet _ _
finitePropKind = record { isFiniteSetoid = PropKind-IsFiniteSet }


--------------------------------------------------------------------------------
--  Subsets of properties over a particular operator code type
--------------------------------------------------------------------------------

record Code k ℓ : Set (sucˡ (k ⊔ˡ ℓ)) where
  field
    finiteAt : ℕ → FiniteSet k ℓ

  module K n = FiniteSet (finiteAt n)
  open K using () renaming (Carrier to K; N to boundAt; isFiniteSetoid to isFiniteAt)

  module Property where
    finiteSet : FiniteSet _ _
    finiteSet = record
      { isFiniteSetoid =
          Σ-isFiniteSetoid PropKind-IsFiniteSet (All-finiteSet boundAt isFiniteAt ∘ opArities)
      }

    open FiniteSet finiteSet public
    open FiniteProps finiteSet public

  allAppliedProperties : List (Property K)
  allAppliedProperties = FiniteSet.enumerate Property.finiteSet

  subCode : ∀ {p} (P : ∀ {n} → K n → Set p) → (∀ {n} → U.Decidable (P {n})) → Code {!!}
  subCode P decP = record
    { K = λ n → ∃ (P {n})
    ; boundAt = {!!}
    ; isFiniteAt = {!!}
    }


record Properties {k} (code : Code k) : Set k where
  constructor properties

  open Code code using (K)

  field
    hasProperty : Property K → Bool

open Properties public

module _ {k} {code : Code k} where
  open Code code using (K; module Property)

  -- Evaluates to 'true' only when every property is present.

  hasAll : Properties code → Bool
  hasAll Π = Property.foldMap BoolExtra.∧-idempotentCommutativeMonoid (hasProperty Π)


  -- Inhabited if the given property is present. Suitable for use as an instance
  -- argument.

  record _∈ₚ_ (π : Property K) (Π : Properties code) : Set where
    instance constructor fromTruth
    field
      truth : T (hasProperty Π π)

  open _∈ₚ_


  -- Inhabited if all the properties are present. Suitable for use as an
  -- instance argument but difficult to work with.

  record ⊨ (Π : Properties code) : Set where
    instance constructor fromTruth
    field
      truth : T (hasAll Π)


  -- Inhabited if all the properties are present. Unsuitable for use as an
  -- implicit argument, but easy to work with.

  ⊢ : Properties code → Set k
  ⊢ Π = ∀ π → π ∈ₚ Π


  -- The two forms of truth are equivalent to each other, as we would hope.

  ⊢→⊨ : {Π : Properties code} → ⊢ Π → ⊨ Π
  ⊢→⊨ {Π} p = ⊨.fromTruth (Equivalence.from T-≡ ⟨$⟩ hasAll-true)
    where
    hasProperty-const : ∀ π → hasProperty Π π ≡ true
    hasProperty-const π = Equivalence.to T-≡ ⟨$⟩ (p π .truth)

    open ≡.Reasoning
    icm = BoolExtra.∧-idempotentCommutativeMonoid

    hasAll-true : hasAll Π ≡ true
    hasAll-true = begin
      hasAll Π                                  ≡⟨⟩
      Property.foldMap icm (hasProperty Π)      ≡⟨ Property.foldMap-cong icm hasProperty-const  ⟩
      Property.foldMap icm (λ _ → true)         ≡⟨ proj₁ (IdempotentCommutativeMonoid.identity icm) _ ⟩
      true ∧ Property.foldMap icm (λ _ → true)  ≡⟨ Property.foldMap-const icm ⟩
      true                                      ∎

  ⊨→⊢ : {Π : Properties code} → ⊨ Π → ⊢ Π
  ⊨→⊢ {Π} t π = fromTruth (Equivalence.from T-≡ ⟨$⟩ hasProperty-true)
    where
      i = Property.toIx π

      open ≡.Reasoning
      icm = BoolExtra.∧-idempotentCommutativeMonoid
      module ∧ = IdempotentCommutativeMonoid icm

      hasAll-true : hasAll Π ≡ true
      hasAll-true = Equivalence.to T-≡ ⟨$⟩ ⊨.truth t

      hasProperty-true : hasProperty Π π ≡ true
      hasProperty-true = begin
        hasProperty Π π            ≡⟨ ≡.sym (proj₂ ∧.identity _ ) ⟩
        hasProperty Π π ∧ true     ≡⟨ ∧.∙-cong (≡.refl {x = hasProperty Π π}) (≡.sym hasAll-true)  ⟩
        hasProperty Π π ∧ hasAll Π ≡⟨ Property.enumTable-complete icm (record { _⟨$⟩_ = hasProperty Π ; cong = λ {(≡.refl , ≡.refl) → ≡.refl}}) π ⟩
        hasAll Π                   ≡⟨ hasAll-true ⟩
        true                       ∎

  -- The empty set of properties

  empty : Properties code
  hasProperty empty _ = false

  -- Form a set of properties from a single property

  singleton : Property K → Properties code
  singleton π = properties λ π′ → ⌊ π Property.≟ π′ ⌋

  -- Union of two sets of properties

  _∪ₚ_ : Properties code → Properties code → Properties code
  hasProperty (Π₁ ∪ₚ Π₂) π = hasProperty Π₁ π ∨ hasProperty Π₂ π

  -- Form a set of properties from a list of properties

  fromList : List (Property K) → Properties code
  fromList = List.foldr (_∪ₚ_ ∘ singleton) empty

  π-∈ₚ-singleton : ∀ {π} → π ∈ₚ singleton π
  truth (π-∈ₚ-singleton {π}) with π Property.≟ π
  truth (π-∈ₚ-singleton {π}) | yes p = _
  truth (π-∈ₚ-singleton {π}) | no ¬p = ¬p (OverΣ.refl ≡.refl)

  _⇒ₚ_ : Properties code → Properties code → Properties code
  hasProperty (Π₁ ⇒ₚ Π₂) π = not (hasProperty Π₁ π) ∨ hasProperty Π₂ π

  ⇒ₚ-MP′ : ∀ {Π₁ Π₂} → ⊢ (Π₁ ⇒ₚ Π₂) → ⊢ Π₁ → ⊢ Π₂
  ⇒ₚ-MP′ {Π₁} {Π₂} f g π = fromTruth (BoolExtra.MP (truth (f π)) (truth (g π)))

  ⇒ₚ-MP : ∀ {Π₁ Π₂} → ⊨ (Π₁ ⇒ₚ Π₂) → ⊨ Π₁ → ⊨ Π₂
  ⇒ₚ-MP has⇒ hasΠ₁ = ⊢→⊨ (⇒ₚ-MP′ (⊨→⊢ has⇒) (⊨→⊢ hasΠ₁))


  -- ⇒ₚ-trans : ∀ {Π₁ Π₂ Π₃} → ⊨ (Π₁ ⇒ₚ Π₂) → ⊨ (Π₂ ⇒ₚ Π₃) → ⊨ (Π₁ ⇒ₚ Π₃)
  -- ⇒ₚ-trans {Π₁} p q = ?


  Has⇒ₚ : ∀ {Π Π′ π} → π ∈ₚ Π′ → ⊨ (Π′ ⇒ₚ Π) → π ∈ₚ Π
  Has⇒ₚ {Π = Π} {Π′} {π} hasπ has⇒ =
    fromTruth (BoolExtra.MP (truth (⊨→⊢ has⇒ π)) (truth hasπ))
