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

data Property {k} (K : ℕ → Set k) : Set k where
  associative commutative idempotent selective cancellative
    : (∙ : K 2) → Property K

  leftIdentity rightIdentity : (ε : K 0) (∙ : K 2) → Property K
  leftZero rightZero : (ω : K 0) (∙ : K 2) → Property K

  _distributesOverˡ_ _distributesOverʳ_ : (* + : K 2) → Property K

finiteProperty : ∀ {c ℓ} → PointwiseFiniteSet ℕ c ℓ → FiniteSet _ _
finiteProperty finiteK = record
  { Carrier = Property K
  ; _≈_ = _≡_
  ; N = N
  ; isFiniteSet = record
    { isEquivalence = ≡.isEquivalence
    ; ontoFin = liftConstructors pieces (Table.lookup args) {!!} {!!}
    }
  }
  where
    module K = PointwiseFiniteSet finiteK
    open K using () renaming (Carrier to K)

    open Nat using (_+_; _*_)
    open Fin using (zero; suc; #_)

    argsL : List (Set _)
    argsL
      = K 2 ∷ K 2 ∷ K 2 ∷ K 2 ∷ K 2
      ∷ (K 0 × K 2) ∷ (K 0 × K 2)
      ∷ (K 0 × K 2) ∷ (K 0 × K 2)
      ∷ (K 2 × K 2) ∷ (K 2 × K 2)
      ∷ []

    count = List.length argsL

    args : Table (Set _) _
    args = Table.fromList argsL

    sizes : Table ℕ _
    sizes = Table.fromList
      ( K.boundAt 2 ∷ K.boundAt 2 ∷ K.boundAt 2 ∷ K.boundAt 2 ∷ K.boundAt 2
      ∷ (K.boundAt 0 * K.boundAt 2) ∷ (K.boundAt 0 * K.boundAt 2)
      ∷ (K.boundAt 0 * K.boundAt 2) ∷ (K.boundAt 0 * K.boundAt 2)
      ∷ (K.boundAt 2 * K.boundAt 2) ∷ (K.boundAt 2 * K.boundAt 2)
      ∷ [])

    mkProperty : ∀ i → Table.lookup args i → Property K
    mkProperty zero = associative
    mkProperty (suc i) x = {!!}

    -- mkProperty : Property K ↞ ∃ (Table.lookup args)
    -- mkProperty =
    --   { to = {!!}
    --   ; from = {!!}
    --   ; left-inverse-of = {!!}
    --   }

    pieces : Pieces ℕ id
    pieces = record
      { numPieces = count
      ; pieces = sizes
      }

    N = Pieces.totalSize pieces

    -- ksize : ∀ {m} (op : K m) → Fin (K.boundAt m)
    -- ksize {m} op = LeftInverse.to (K.ontoFin m) ⟨$⟩ op
    -- inj = intoPiece² pieces

    -- inj* : ∀ {m n} → Fin m → Fin n → Fin (m * n)
    -- inj* zero j = Fin.inject+ _ j
    -- inj* {n = n} (suc i) j = Fin.raise n (inj* i j)

    -- to : Property K → Fin N
    -- to (associative ∙)        = inj (# 0) (# 0) (ksize ∙)
    -- to (commutative ∙)        = inj (# 0) (# 1) (ksize ∙)
    -- to (idempotent ∙)         = inj (# 0) (# 2) (ksize ∙)
    -- to (selective ∙)          = inj (# 0) (# 3) (ksize ∙)
    -- to (cancellative ∙)       = inj (# 0) (# 4) (ksize ∙)
    -- to (leftIdentity ε ∙)     = inj (# 1) (# 0) (inj* (ksize ε) (ksize ∙))
    -- to (rightIdentity ε ∙)    = inj (# 1) (# 1) (inj* (ksize ε) (ksize ∙))
    -- to (leftZero ω ∙)         = inj (# 1) (# 2) (inj* (ksize ω) (ksize ∙))
    -- to (rightZero ω ∙)        = inj (# 1) (# 3) (inj* (ksize ω) (ksize ∙))
    -- to (* distributesOverˡ +) = inj (# 2) (# 0) (inj* (ksize *) (ksize +))
    -- to (* distributesOverʳ +) = inj (# 2) (# 1) (inj* (ksize *) (ksize +))

    -- bij₁ : Σ (Fin 3) (λ i → Fin (Pieces.totalSize (Pieces.pieceAt pieces i))) ↔ Fin N
    -- bij₁ = asPiece pieces

    -- bij₂ : Σ (Fin 3) (λ i →
    --                      Σ (Fin (Pieces.numPieces (Pieces.pieceAt pieces i)))
    --                      (Fin ∘ Pieces.sizeAt (Pieces.pieceAt pieces i))) ↔ Fin N
    -- bij₂ = asPiece² pieces


module _ {k′} {F : Set k′ → Set k′} (applicative : RawApplicative F) where
  open RawApplicative applicative

  traverseProperty : ∀ {k} {K : ℕ → Set k} {K′ : ℕ → Set k′} → (∀ {n} → K n → F (K′ n)) → Property K → F (Property K′)
  traverseProperty f (associative ∙)        = pure associative ⊛ f ∙
  traverseProperty f (commutative ∙)        = pure commutative ⊛ f ∙
  traverseProperty f (idempotent ∙)         = pure idempotent ⊛ f ∙
  traverseProperty f (selective ∙)          = pure selective ⊛ f ∙
  traverseProperty f (cancellative ∙)       = pure cancellative ⊛ f ∙
  traverseProperty f (leftIdentity ε ∙)     = pure leftIdentity ⊛ f ε ⊛ f ∙
  traverseProperty f (rightIdentity ε ∙)    = pure rightIdentity ⊛ f ε ⊛ f ∙
  traverseProperty f (leftZero ω ∙)         = pure leftZero ⊛ f ω ⊛ f ∙
  traverseProperty f (rightZero ω ∙)        = pure rightZero ⊛ f ω ⊛ f ∙
  traverseProperty f (* distributesOverˡ +) = pure _distributesOverˡ_ ⊛ f * ⊛ f +
  traverseProperty f (* distributesOverʳ +) = pure _distributesOverʳ_ ⊛ f * ⊛ f +

-- mapProperty : ∀ {k k′} {K : ℕ → Set k} {K′ : ℕ → Set k′} → (∀ {n} → K n → K′ n) → Property K → Property K′

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
--  Subsets of properties over a particular operator code type
--------------------------------------------------------------------------------

-- record Code k : Set (sucˡ k) where
--   field
--     K : ℕ → Set k
--     countAtArity : ℕ → ℕ
--     injAtArity : ∀ n → K n ↣ Fin (countAtArity n)

--   Property′ = Property K

--   -- TODO: Automate this with reflection. Also proofs of completeness.
--   allProperties : List Property′
--   allProperties =
--     let open List

--         p2 : K 2 → List Property′
--         p2 ∙
--           = associative ∙
--           ∷ commutative ∙
--           ∷ idempotent ∙
--           ∷ selective ∙
--           ∷ cancellative ∙
--           ∷ []
--         p02 : K 0 → K 2 → List Property′
--         p02 α ∙
--           = leftIdentity α ∙
--           ∷ rightIdentity α ∙
--           ∷ leftZero α ∙
--           ∷ rightZero α ∙
--           ∷ []
--         p22 : K 2 → K 2 → List Property′
--         p22 + *
--           = * distributesOverˡ +
--           ∷ * distributesOverʳ +
--           ∷ []

--         all0 : List (K 0)
--         all0 = {!!}

--         all2 : List (K 2)
--         all2 = {!!}
--     in   concatMap (λ ∙ →
--        p2 ∙
--          ++ concatMap (λ α →
--        p02 α ∙
--          ) all0) all2 ++
--          concatMap (λ + → concatMap (λ * →
--        p22 + *
--          ) all2) all2

-- open Code using (Property′)

-- open Bool

-- record Properties {k} (code : Code k) : Set k where
--   constructor properties

--   open Code code

--   field
--     hasProperty : Property K → Bool

--   HasProperty : Property K → Set
--   HasProperty π = T (hasProperty π)

--   hasAll : Bool
--   hasAll = List.foldr (λ π → hasProperty π ∧_) true allProperties

--   HasAll : Set
--   HasAll = T hasAll

-- open Properties public

-- _∈ₚ_ : ∀ {k} {code : Code k} → Property′ code → Properties code → Set
-- π ∈ₚ Π = HasProperty Π π

-- _⇒ₚ_ : ∀ {k} {code : Code k} → Properties code → Properties code → Properties code
-- hasProperty (Π₁ ⇒ₚ Π₂) π = not (hasProperty Π₁ π) ∨ hasProperty Π₂ π


-- -- Has⇒ₚ : ∀ {k} {code : Code k} {Π Π′ : Properties code} {π : Property (Code.K code)} → π ∈ₚ Π′ → HasAll (Π′ ⇒ₚ Π) → π ∈ₚ Π
-- -- Has⇒ₚ {Π = Π} {Π′} {π} hasπ hasΠ′ with hasProperty Π π | hasAll 
-- -- Has⇒ₚ hasπ hasΠ′ = {!hasΠ′!}

-- instance
--   truth : ⊤
--   truth = tt

--   -- T-HasProperty : ∀ {k} {K : ℕ → Set k} {Π : Properties K} {π} ⦃ isTrue : T (hasProperty Π π) ⦄ → π ∈ₚ Π
--   -- T-HasProperty {Π = Π} {π} ⦃ isTrue ⦄ with hasProperty Π π
--   -- T-HasProperty {Π = _} {_} ⦃ () ⦄ | false
--   -- T-HasProperty {Π = _} {_} ⦃ tt ⦄ | true = tt

-- --------------------------------------------------------------------------------
-- --  Structures with additional properties
-- --------------------------------------------------------------------------------

-- record Struct c ℓ {k} {code : Code k} (Π : Properties code) : Set (sucˡ (c ⊔ˡ ℓ ⊔ˡ k)) where
--   open Code code

--   field
--     rawStruct : RawStruct c ℓ K
--     Π-hold : ∀ {π} → π ∈ₚ Π → ⟦ π ⟧P rawStruct

--   open RawStruct rawStruct public

--   has : Property K → Set
--   has π = π ∈ₚ Π

--   has′ : Properties code → Set
--   has′ Π′ = HasAll (Π ⇒ₚ Π′)

--   use : (π : Property K) ⦃ hasπ : has π ⦄ → ⟦ π ⟧P rawStruct
--   use π ⦃ hasπ ⦄ = Π-hold hasπ

--   -- from : (Π′ : Properties code) (π : Property K) ⦃ hasπ : π ∈ₚ Π′ ⦄ ⦃ hasΠ′ : has′ Π′ ⦄ → ⟦ π ⟧P rawStruct
--   -- from Π′ π ⦃ hasπ ⦄ ⦃ hasΠ′ ⦄ = use π ⦃ {!!} ⦄

-- --------------------------------------------------------------------------------
-- --  Some named property combinations
-- --------------------------------------------------------------------------------

-- private
--   Maybe-applicative : ∀ {ℓ} → RawApplicative {ℓ} Maybe
--   Maybe-applicative = record
--     { pure = just
--     ; _⊛_ = maybe Maybe.map λ _ → nothing
--     }

-- subΠ : ∀ {k k′} {code : Code k} {code′ : Code k′} →
--   let open Code code using (K)
--       open Code code′ using () renaming (K to K′)
--   in (∀ {n} → K′ n → Maybe (K n)) →
--      Properties code → Properties code′ → Properties code′
-- hasProperty (subΠ f Π₀ Π₁) π with traverseProperty Maybe-applicative f π
-- hasProperty (subΠ f Π₀ Π₁) π | just π′ = hasProperty Π₀ π′
-- hasProperty (subΠ f Π₀ Π₁) π | nothing = hasProperty Π₁ π

-- data MagmaK : ℕ → Set where
--   ∙ : MagmaK 2

-- data MonoidK : ℕ → Set where
--   ε : MonoidK 0
--   ∙ : MonoidK 2

-- data BimonoidK : ℕ → Set where
--   0# 1# : BimonoidK 0
--   + * : BimonoidK 2

-- module _ where
--   open Code
--   open ℕ

--   magmaCode : Code _
--   K magmaCode = MagmaK
--   allAtArity magmaCode (suc (suc zero)) = ∙ ∷ []
--   allAtArity magmaCode _ = []

--   monoidCode : Code _
--   K monoidCode = MonoidK
--   allAtArity monoidCode zero = ε ∷ []
--   allAtArity monoidCode (suc (suc zero)) = ∙ ∷ []
--   allAtArity monoidCode _ = []

--   bimonoidCode : Code _
--   K bimonoidCode = BimonoidK
--   allAtArity bimonoidCode zero = 0# ∷ 1# ∷ []
--   allAtArity bimonoidCode (suc (suc zero)) = + ∷ * ∷ []
--   allAtArity bimonoidCode _ = []

-- +-part : ∀ {n} → BimonoidK n → Maybe (MonoidK n)
-- +-part 0# = just ε
-- +-part + = just ∙
-- +-part _ = nothing

-- *-part : ∀ {n} → BimonoidK n → Maybe (MonoidK n)
-- *-part 1# = just ε
-- *-part * = just ∙
-- *-part _ = nothing

-- isSemigroup : Properties magmaCode
-- isSemigroup = properties
--   λ { (associative ∙) → true
--     ; _ → false}

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
