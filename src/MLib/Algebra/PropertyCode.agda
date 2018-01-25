module MLib.Algebra.PropertyCode where

open import MLib.Prelude
open import MLib.Algebra.Instances

open import Relation.Binary as B using (Setoid)

open List using (_∷_; [])
open import Data.List.All as All using (All; _∷_; []) public
open import Data.List.Any using (Any; here; there)
open import Data.List.Any.Membership.Propositional using (_∈_)

--------------------------------------------------------------------------------
--  Is<Structure>
--------------------------------------------------------------------------------

record IsMagma {c ℓ} {A : Set c} (≈ : Rel A ℓ) (∙ : A → A → A) : Set (c ⊔ˡ ℓ) where
  open Algebra.FunctionProperties ≈
  field
    isEquivalence : IsEquivalence ≈
    ∙-cong : Congruent₂ ∙

  setoid : Setoid _ _
  setoid = record { isEquivalence = isEquivalence }

  open IsEquivalence isEquivalence public

record IsBimagma {c ℓ} {A : Set c} (≈ : Rel A ℓ) (+ * : A → A → A) : Set (c ⊔ˡ ℓ) where
  open Algebra.FunctionProperties ≈
  field
    isEquivalence : IsEquivalence ≈
    +-cong : Congruent₂ +
    *-cong : Congruent₂ *

  setoid : Setoid _ _
  setoid = record { isEquivalence = isEquivalence }

  +-isMagma : IsMagma ≈ +
  +-isMagma = record { isEquivalence = isEquivalence ; ∙-cong = +-cong }

  *-isMagma : IsMagma ≈ *
  *-isMagma = record { isEquivalence = isEquivalence ; ∙-cong = *-cong }

  open IsEquivalence isEquivalence public

--------------------------------------------------------------------------------
--  Structures
--------------------------------------------------------------------------------

record Magma c ℓ : Set (sucˡ (c ⊔ˡ ℓ)) where
  infix 4 _≈_
  infixl 7 _∙_

  field
    Carrier : Set c
    _≈_ : Rel Carrier ℓ
    _∙_ : Carrier → Carrier → Carrier
    isMagma : IsMagma _≈_ _∙_

  open IsMagma isMagma public

record Bimagma c ℓ : Set (sucˡ (c ⊔ˡ ℓ)) where
  infix 4 _≈_
  infixl 6 _+_
  infixl 7 _*_

  field
    Carrier : Set c
    _≈_ : Rel Carrier ℓ
    _+_ : Carrier → Carrier → Carrier
    _*_ : Carrier → Carrier → Carrier
    isBimagma : IsBimagma _≈_ _+_ _*_

  open IsBimagma isBimagma public

  +-magma : Magma _ _
  +-magma = record { isMagma = +-isMagma }

  *-magma : Magma _ _
  *-magma = record { isMagma = *-isMagma }

--------------------------------------------------------------------------------
--  Property codes
--------------------------------------------------------------------------------

data MagmaProperty {s} (Σ₀ : Set s) : Set s where
  associative commutative idempotent
    : MagmaProperty Σ₀
  identity zero : Σ₀ → MagmaProperty Σ₀

data BimagmaProperty {s} (Σ₀ : Set s) : Set s where
  leftDistributive rightDistributive
    : BimagmaProperty Σ₀
  on+ on* : MagmaProperty Σ₀ → BimagmaProperty Σ₀

module Interpret {s} {Σ₀ : Set s} where
  module _ {c ℓ} (magma : Magma c ℓ) (⟦_⟧ : Σ₀ → Magma.Carrier magma) where
    open Magma magma
    open Algebra.FunctionProperties _≈_

    ⟦_,_⊢_⟧M : MagmaProperty Σ₀ → Set (c ⊔ˡ ℓ)
    ⟦_,_⊢_⟧M associative = Associative _∙_
    ⟦_,_⊢_⟧M commutative = Commutative _∙_
    ⟦_,_⊢_⟧M idempotent = Idempotent _∙_
    ⟦_,_⊢_⟧M (identity ε₀) = Identity ⟦ ε₀ ⟧ _∙_
    ⟦_,_⊢_⟧M (zero ω₀) = Zero ⟦ ω₀ ⟧ _∙_

  module _ {c ℓ} (bimagma : Bimagma c ℓ) (⟦_⟧ : Σ₀ → Bimagma.Carrier bimagma) where
    open Bimagma bimagma
    open Algebra.FunctionProperties _≈_

    ⟦_,_⊢_⟧B : BimagmaProperty Σ₀ → Set (c ⊔ˡ ℓ)
    ⟦_,_⊢_⟧B leftDistributive = _*_ DistributesOverˡ _+_
    ⟦_,_⊢_⟧B rightDistributive = _*_ DistributesOverʳ _+_
    ⟦_,_⊢_⟧B (on+ c) = ⟦ +-magma , ⟦_⟧ ⊢ c ⟧M
    ⟦_,_⊢_⟧B (on* c) = ⟦ *-magma , ⟦_⟧ ⊢ c ⟧M

-- module Interpret where
--   from+ : BimagmaProperty → Maybe MagmaProperty
--   from+ (on+ c) = just c
--   from+ _ = nothing

--   from* : BimagmaProperty → Maybe MagmaProperty
--   from* (on* c) = just c
--   from* _ = nothing

--   from+-interpret : ∀ {c ℓ} (bimagma : Bimagma c ℓ) {b} {m} → from+ b ≡ just m →
--     let open Bimagma bimagma
--     in ⟦ b ⟧B bimagma → ⟦ m ⟧M +-magma
--   from+-interpret bimagma {on+ x} ≡.refl p = p
--   from+-interpret bimagma {leftDistributive} () p
--   from+-interpret bimagma {rightDistributive} () p
--   from+-interpret bimagma {on* x} () p

--   from*-interpret : ∀ {c ℓ} (bimagma : Bimagma c ℓ) {b} {m} → from* b ≡ just m →
--     let open Bimagma bimagma
--     in ⟦ b ⟧B bimagma → ⟦ m ⟧M *-magma
--   from*-interpret bimagma {on* x} ≡.refl p = p
--   from*-interpret bimagma {leftDistributive} () p
--   from*-interpret bimagma {rightDistributive} () p
--   from*-interpret bimagma {on+ x} () p

-- --------------------------------------------------------------------------------
-- --  Structures with additional properties
-- --------------------------------------------------------------------------------

-- record Dagma (propCodes : List MagmaProperty) c ℓ : Set (sucˡ (c ⊔ˡ ℓ)) where
--   field
--     magma : Magma c ℓ
--     properties : All (interpretInM magma) propCodes

--   open Magma magma public

--   -- We can 'use' any property that the algebra is equipped with to get easy
--   -- access to it

--   has : MagmaProperty → Set
--   has prop = prop ∈ propCodes

--   has′ : List MagmaProperty → Set
--   has′ props = All (_∈ propCodes) props

--   use : (prop : MagmaProperty) ⦃ hasProp : has prop ⦄ → ⟦ prop ⟧M magma
--   use _ ⦃ hasProperty ⦄ = All.lookup properties hasProperty

--   from : (props : List MagmaProperty) (prop : MagmaProperty) ⦃ hasProp : prop ∈ props ⦄ ⦃ hasProps : props ⊆ propCodes ⦄ → ⟦ prop ⟧M magma
--   from .(prop ∷ _) prop ⦃ here ≡.refl ⦄ ⦃ p ∷ hasProps ⦄ = use prop ⦃ p ⦄
--   from .(_ ∷ _) prop ⦃ there hasProp ⦄ ⦃ _ ∷ hasProps ⦄ = from _ prop ⦃ hasProp ⦄ ⦃ hasProps ⦄

--   -- If the algebra has an identity, it can be cumbersome to 'use' it, so these
--   -- shortcuts help

--   open Algebra.FunctionProperties _≈_

--   ε : ⦃ hasHasIdentity : has hasIdentity ⦄ → Carrier
--   ε = proj₁ (use hasIdentity)

--   identity : ⦃ hasHasIdentity : has hasIdentity ⦄ → Identity ε _∙_
--   identity = proj₂ (use hasIdentity)

-- record Bidagma (propCodes : List BimagmaProperty) c ℓ : Set (sucˡ (c ⊔ˡ ℓ)) where
--   field
--     bimagma : Bimagma c ℓ
--     properties : All (interpretInB bimagma) propCodes

--   open Bimagma bimagma public

--   has : BimagmaProperty → Set
--   has prop = prop ∈ propCodes

--   has′ : List BimagmaProperty → Set
--   has′ props = All (_∈ propCodes) props

--   use : (prop : BimagmaProperty) ⦃ hasProp : has prop ⦄ → ⟦ prop ⟧B bimagma
--   use _ ⦃ hasProp ⦄ = All.lookup properties hasProp

--   +-propCodes : List MagmaProperty
--   +-propCodes = List.mapMaybe Interpret.from+ propCodes

--   *-propCodes : List MagmaProperty
--   *-propCodes = List.mapMaybe Interpret.from* propCodes

--   private
--     allMapMaybe :
--       ∀ {a b p q} {A : Set a} {B : Set b}
--         {Σ₀ : A → Set p} {Q : B → Set q} {f : A → Maybe B} (p : ∀ {x y} → f x ≡ just y → Σ₀ x → Q y)
--         {xs : List A} → All Σ₀ xs → All Q (List.mapMaybe f xs)
--     allMapMaybe p [] = []
--     allMapMaybe {f = f} p (_∷_ {x} px ap) with f x | ≡.inspect f x
--     allMapMaybe p (_∷_ {_} px ap) | just y | ≡.[ eq ] = p eq px ∷ allMapMaybe p ap
--     allMapMaybe p (_∷_ {_} px ap) | nothing | _ = allMapMaybe p ap

--   +-dagma : Dagma +-propCodes c ℓ
--   +-dagma = record { magma = +-magma ; properties = allMapMaybe (Interpret.from+-interpret bimagma) properties  }

--   *-dagma : Dagma *-propCodes c ℓ
--   *-dagma = record { magma = *-magma ; properties = allMapMaybe (Interpret.from*-interpret bimagma) properties  }

--   open Dagma +-dagma public
--     using ()
--     renaming
--     ( properties to +-properties
--     ; has to +-has
--     ; has′ to +-has′
--     ; use to +-use
--     ; ε to 0#
--     ; identity to +-identity
--     )

--   open Dagma *-dagma public
--     using ()
--     renaming
--     ( properties to *-properties
--     ; has to *-has
--     ; has′ to *-has′
--     ; use to *-use
--     ; ε to 1#
--     ; identity to *-identity
--     )

--   open Algebra.FunctionProperties _≈_

--   0#′ : ⦃ _ : *-has hasZero ⦄ → Carrier
--   0#′ = proj₁ (*-use hasZero)

--   zero′ : ⦃ _ : *-has hasZero ⦄ → Zero 0#′ _*_
--   zero′ = proj₂ (*-use hasZero)

--   -- -- If a zero for * and an identity for + both exist, they are equal so long as
--   -- -- the bimagma is distributive
--   -- 0#≈0#′ : ⦃ _ : +-has hasIdentity ⦄ ⦃ _ : *-has hasZero ⦄ ⦃ _ : has rightDistributive ⦄ → 0# ≈ 0#′
--   -- 0#≈0#′ =
--   --   begin
--   --     0#                      ≈⟨ ? ⟩
--   --     0# + 0#                 ≈⟨ ? ⟩
--   --     0#′                     ∎
--   --   where open EqReasoning setoid

-- --------------------------------------------------------------------------------
-- --  Some named property combinations
-- --------------------------------------------------------------------------------

-- isSemigroup : List MagmaProperty
-- isSemigroup = associative ∷ []

-- isMonoid : List MagmaProperty
-- isMonoid = hasIdentity ∷ isSemigroup

-- isCommutativeMonoid : List MagmaProperty
-- isCommutativeMonoid = commutative ∷ isMonoid

-- isSemiring : List BimagmaProperty
-- isSemiring
--   =  map on+ isCommutativeMonoid
--   ++ map on* isMonoid
--   ++ leftDistributive
--    ∷ rightDistributive
--    ∷ on* hasZero
--    ∷ []
--   where open List

-- module Into where
--   open Algebra using (Semigroup; Monoid; CommutativeMonoid)

--   infixl 0 _↓M_

--   _↓M_ : ∀ {c ℓ} {strongProps} → Dagma strongProps c ℓ → ∀ weakProps ⦃ sub : weakProps ⊆ strongProps ⦄ → Dagma weakProps c ℓ
--   _↓M_ dagma _ ⦃ sub ⦄ = record
--     { magma = magma
--     ; properties = getAll⊆ sub properties
--     }
--     where open Dagma dagma

--   _↓B_ : ∀ {c ℓ} {strongProps} → Bidagma strongProps c ℓ → ∀ weakProps ⦃ sub : weakProps ⊆ strongProps ⦄ → Bidagma weakProps c ℓ
--   _↓B_ bidagma _ ⦃ sub ⦄ = record
--     { bimagma = bimagma
--     ; properties = getAll⊆ sub properties
--     }
--     where open Bidagma bidagma

--   semigroup : ∀ {c ℓ} {props} ⦃ _ : isSemigroup ⊆ props ⦄ → Dagma props c ℓ → Semigroup c ℓ
--   semigroup dagma = record
--     { isSemigroup = record
--       { isEquivalence = isEquivalence
--       ; assoc = from isSemigroup associative
--       ; ∙-cong = ∙-cong
--       }
--     }
--     where open Dagma dagma

--   monoid : ∀ {c ℓ} {props} ⦃ _ : isMonoid ⊆ props ⦄ → Dagma props c ℓ → Monoid c ℓ
--   monoid ⦃ mon ⦄ dagma = record
--     { isMonoid = record
--       { isSemigroup = S.isSemigroup
--       ; identity = proj₂ (from isMonoid hasIdentity)
--       }
--     }
--     where
--       open Dagma dagma
--       module S = Semigroup (semigroup (dagma ↓M isMonoid ↓M isSemigroup))

--   commutativeMonoid : ∀ {c ℓ} {props} ⦃ _ : isCommutativeMonoid ⊆ props ⦄ → Dagma props c ℓ → CommutativeMonoid c ℓ
--   commutativeMonoid dagma = record
--     { isCommutativeMonoid = record
--       { isSemigroup = S.isSemigroup
--       ; identityˡ = proj₁ (proj₂ (from isCommutativeMonoid hasIdentity))
--       ; comm = from isCommutativeMonoid commutative
--       }
--     }
--     where
--       open Dagma dagma
--       module S = Semigroup (semigroup (dagma ↓M isCommutativeMonoid ↓M isSemigroup))

--   -- semiring
