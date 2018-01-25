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

data MagmaProperty : Set where
  associative commutative idempotent hasIdentity
    : MagmaProperty

data BimagmaProperty : Set where
  leftDistributive rightDistributive : BimagmaProperty
  on+ on* : MagmaProperty → BimagmaProperty

⟦_⟧M : ∀ {c ℓ} → MagmaProperty → Magma c ℓ → Set (c ⊔ˡ ℓ)
⟦_⟧M {c} {ℓ} code magma = interpret code
  where
    open Magma magma
    open Algebra.FunctionProperties _≈_

    interpret : MagmaProperty → Set (c ⊔ˡ ℓ)
    interpret associative = Associative _∙_
    interpret commutative = Commutative _∙_
    interpret idempotent = Idempotent _∙_
    interpret hasIdentity = ∃ λ ε → Identity ε _∙_

interpretInM : ∀ {c ℓ} → Magma c ℓ → MagmaProperty → Set (c ⊔ˡ ℓ)
interpretInM = Function.flip ⟦_⟧M

⟦_⟧B : ∀ {c ℓ} → BimagmaProperty → Bimagma c ℓ → Set (c ⊔ˡ ℓ)
⟦_⟧B {c} {ℓ} code bimagma = interpret code
  where
    open Bimagma bimagma
    open Algebra.FunctionProperties _≈_

    interpret : BimagmaProperty → Set (c ⊔ˡ ℓ)
    interpret leftDistributive = _*_ DistributesOverˡ _+_
    interpret rightDistributive = _*_ DistributesOverʳ _+_
    interpret (on+ c) = ⟦ c ⟧M +-magma
    interpret (on* c) = ⟦ c ⟧M *-magma

interpretInB : ∀ {c ℓ} → Bimagma c ℓ → BimagmaProperty → Set (c ⊔ˡ ℓ)
interpretInB = Function.flip ⟦_⟧B

module Interpret where
  from+ : BimagmaProperty → Maybe MagmaProperty
  from+ (on+ c) = just c
  from+ _ = nothing

  from* : BimagmaProperty → Maybe MagmaProperty
  from* (on* c) = just c
  from* _ = nothing

  from+-interpret : ∀ {c ℓ} (bimagma : Bimagma c ℓ) {b} {m} → from+ b ≡ just m →
    let open Bimagma bimagma
    in ⟦ b ⟧B bimagma → ⟦ m ⟧M +-magma
  from+-interpret bimagma {on+ x} ≡.refl p = p
  from+-interpret bimagma {leftDistributive} () p
  from+-interpret bimagma {rightDistributive} () p
  from+-interpret bimagma {on* x} () p

  from*-interpret : ∀ {c ℓ} (bimagma : Bimagma c ℓ) {b} {m} → from* b ≡ just m →
    let open Bimagma bimagma
    in ⟦ b ⟧B bimagma → ⟦ m ⟧M *-magma
  from*-interpret bimagma {on* x} ≡.refl p = p
  from*-interpret bimagma {leftDistributive} () p
  from*-interpret bimagma {rightDistributive} () p
  from*-interpret bimagma {on+ x} () p

--------------------------------------------------------------------------------
--  Structures with additional properties
--------------------------------------------------------------------------------

record Dagma (propCodes : List MagmaProperty) c ℓ : Set (sucˡ (c ⊔ˡ ℓ)) where
  field
    magma : Magma c ℓ
    properties : All (interpretInM magma) propCodes

  open Magma magma public

  -- We can 'use' any property that the algebra is equipped with to get easy
  -- access to it

  has : MagmaProperty → Set
  has prop = prop ∈ propCodes

  has′ : List MagmaProperty → Set
  has′ props = All (_∈ propCodes) props

  use : (prop : MagmaProperty) ⦃ hasProp : has prop ⦄ → ⟦ prop ⟧M magma
  use _ ⦃ hasProperty ⦄ = All.lookup properties hasProperty

  from : (props : List MagmaProperty) (prop : MagmaProperty) ⦃ hasProp : prop ∈ props ⦄ ⦃ hasProps : props ⊆ propCodes ⦄ → ⟦ prop ⟧M magma
  from .(prop ∷ _) prop ⦃ here ≡.refl ⦄ ⦃ p ∷ hasProps ⦄ = use prop ⦃ p ⦄
  from .(_ ∷ _) prop ⦃ there hasProp ⦄ ⦃ _ ∷ hasProps ⦄ = from _ prop ⦃ hasProp ⦄ ⦃ hasProps ⦄

  -- If the algebra has an identity, it can be cumbersome to 'use' it, so these
  -- shortcuts help

  open Algebra.FunctionProperties _≈_

  ε : ⦃ hasHasIdentity : has hasIdentity ⦄ → Carrier
  ε = proj₁ (use hasIdentity)

  identity : ⦃ hasHasIdentity : has hasIdentity ⦄ → Identity ε _∙_
  identity = proj₂ (use hasIdentity)

record Bidagma (propCodes : List BimagmaProperty) c ℓ : Set (sucˡ (c ⊔ˡ ℓ)) where
  field
    bimagma : Bimagma c ℓ
    properties : All (interpretInB bimagma) propCodes

  open Bimagma bimagma public

  has : BimagmaProperty → Set
  has prop = prop ∈ propCodes

  has′ : List BimagmaProperty → Set
  has′ props = All (_∈ propCodes) props

  use : (prop : BimagmaProperty) ⦃ hasProp : has prop ⦄ → ⟦ prop ⟧B bimagma
  use _ ⦃ hasProp ⦄ = All.lookup properties hasProp

  +-propCodes : List MagmaProperty
  +-propCodes = List.mapMaybe Interpret.from+ propCodes

  *-propCodes : List MagmaProperty
  *-propCodes = List.mapMaybe Interpret.from* propCodes

  private
    allMapMaybe :
      ∀ {a b p q} {A : Set a} {B : Set b}
        {P : A → Set p} {Q : B → Set q} {f : A → Maybe B} (p : ∀ {x y} → f x ≡ just y → P x → Q y)
        {xs : List A} → All P xs → All Q (List.mapMaybe f xs)
    allMapMaybe p [] = []
    allMapMaybe {f = f} p (_∷_ {x} px ap) with f x | ≡.inspect f x
    allMapMaybe p (_∷_ {_} px ap) | just y | ≡.[ eq ] = p eq px ∷ allMapMaybe p ap
    allMapMaybe p (_∷_ {_} px ap) | nothing | _ = allMapMaybe p ap

  +-dagma : Dagma +-propCodes c ℓ
  +-dagma = record { magma = +-magma ; properties = allMapMaybe (Interpret.from+-interpret bimagma) properties  }

  *-dagma : Dagma *-propCodes c ℓ
  *-dagma = record { magma = *-magma ; properties = allMapMaybe (Interpret.from*-interpret bimagma) properties  }

  open Dagma +-dagma public
    using ()
    renaming
    ( properties to +-properties
    ; has to +-has
    ; has′ to +-has′
    ; use to +-use
    ; ε to 0#
    ; identity to +-identity
    )

  open Dagma *-dagma public
    using ()
    renaming
    ( properties to *-properties
    ; has to *-has
    ; has′ to *-has′
    ; use to *-use
    ; ε to 1#
    ; identity to *-identity
    )

--------------------------------------------------------------------------------
--  Some named property combinations
--------------------------------------------------------------------------------

isSemigroup : List MagmaProperty
isSemigroup = associative ∷ []

isMonoid : List MagmaProperty
isMonoid = hasIdentity ∷ isSemigroup

isCommutativeMonoid : List MagmaProperty
isCommutativeMonoid = commutative ∷ isMonoid

module Into where
  open Algebra using (Semigroup; Monoid; CommutativeMonoid)

  dagma↓ : ∀ {c ℓ} weakProps {strongProps} ⦃ sub : weakProps ⊆ strongProps ⦄ → Dagma strongProps c ℓ → Dagma weakProps c ℓ
  dagma↓ _ ⦃ sub ⦄ dagma = record
    { magma = magma
    ; properties = getAll⊆ sub properties
    }
    where open Dagma dagma

  semigroup : ∀ {c ℓ} {props} ⦃ _ : isSemigroup ⊆ props ⦄ → Dagma props c ℓ → Semigroup c ℓ
  semigroup dagma = record
    { isSemigroup = record
      { isEquivalence = isEquivalence
      ; assoc = from isSemigroup associative
      ; ∙-cong = ∙-cong
      }
    }
    where open Dagma dagma

  monoid : ∀ {c ℓ} {props} ⦃ _ : isMonoid ⊆ props ⦄ → Dagma props c ℓ → Monoid c ℓ
  monoid ⦃ mon ⦄ dagma = record
    { isMonoid = record
      { isSemigroup = S.isSemigroup
      ; identity = proj₂ (from isMonoid hasIdentity)
      }
    }
    where
      open Dagma dagma
      module S = Semigroup (semigroup (dagma↓ isSemigroup (dagma↓ isMonoid dagma)))

  commutativeMonoid : ∀ {c ℓ} {props} ⦃ _ : isCommutativeMonoid ⊆ props ⦄ → Dagma props c ℓ → CommutativeMonoid c ℓ
  commutativeMonoid dagma = record
    { isCommutativeMonoid = record
      { isSemigroup = S.isSemigroup
      ; identityˡ = proj₁ (proj₂ (from isCommutativeMonoid hasIdentity))
      ; comm = from isCommutativeMonoid commutative
      }
    }
    where
      open Dagma dagma
      module S = Semigroup (semigroup (dagma↓ isSemigroup (dagma↓ isCommutativeMonoid dagma)))
