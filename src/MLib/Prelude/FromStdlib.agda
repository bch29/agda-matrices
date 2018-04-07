module MLib.Prelude.FromStdlib where

--------------------------------------------------------------------------------
--  Misc
--------------------------------------------------------------------------------

open import Level public
  using (Level)
  renaming ( zero to zeroˡ; suc to sucˡ; _⊔_ to _⊔ˡ_
           ; Lift to Liftˡ; lift to liftˡ; lower to lowerˡ)

--------------------------------------------------------------------------------
--  Data
--------------------------------------------------------------------------------

open import Data.Product public
  using (Σ; _×_; _,_; proj₁; proj₂; ∃; ∃₂; curry; uncurry)
open import Data.Sum public
  using (_⊎_; inj₁; inj₂)

open import Data.Unit public
  using (⊤; tt)
open import Data.Empty public
  using (⊥; ⊥-elim)

module Bool where
  open import Data.Bool public
  open import Data.Bool.Properties public
open Bool using (Bool; true; false; if_then_else_) hiding (module Bool) public

module Nat where
  open import Data.Nat public
  open import Data.Nat.Properties public
open Nat using (ℕ) hiding (module ℕ) public

module Maybe where
  open import Data.Maybe public
open Maybe using (Maybe; just; nothing; maybe) hiding (module Maybe) public

module List where
  open import Data.List public
  open import Data.List.Properties public
open List using (List; _∷_; []) hiding (module List) public

module Table where
  open import Data.Table public
  open import Data.Table.Properties public
  open import Data.Table.Relation.Equality public
open Table using (Table; tabulate; lookup) hiding (module Table) public

--------------------------------------------------------------------------------
--  Combinators
--------------------------------------------------------------------------------

module Function where
  open import Function public
open Function using (id; _∘_; case_of_) public

--------------------------------------------------------------------------------
--  Relations
--------------------------------------------------------------------------------

open import Relation.Nullary public
  using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable public
  using (⌊_⌋)

-- Export names that can only apply to binary relations; things like 'Decidable'
-- can apply to nullary or unary relations too!
open import Relation.Binary.Core public
  using (Reflexive; Symmetric; Transitive; Irreflexive; Antisymmetric; Asymmetric; Trichotomous)
open import Relation.Binary public
  using (Rel; Setoid; IsEquivalence; Poset; IsPartialOrder)

module EqReasoning {c ℓ} (setoid : Setoid c ℓ) where
  open import Relation.Binary.EqReasoning setoid public

module ≡ where
  open import Relation.Binary.PropositionalEquality public
  module Reasoning = ≡-Reasoning
open ≡ using (_≡_) public

--------------------------------------------------------------------------------
--  Algebra
--------------------------------------------------------------------------------

module Algebra where
  open import Algebra public
  open import Algebra.Structures public
  module FunctionProperties {a ℓ} {A : Set a} (_≈_ : Rel A ℓ) where
    open import Algebra.FunctionProperties _≈_ public

--------------------------------------------------------------------------------
--  From Holes.Prelude
--------------------------------------------------------------------------------

open import Holes.Prelude public using
  ( RawMonad
  ; _>>=_
  ; return
  ; _<$>_
  ; join

  ; RawTraversable
  ; traverse
  ; sequence

  ; Choice
  ; _<|>_
  )

infixl 1 _>>=ₘ_ _>>=ₗ_

_>>=ₘ_ : ∀ {a b} {A : Set a} {B : Set b} → Maybe A → (A → Maybe B) → Maybe B
nothing >>=ₘ _ = nothing
just x >>=ₘ f = f x

_>>=ₗ_ : ∀ {a b} {A : Set a} {B : Set b} → List A → (A → List B) → List B
[] >>=ₗ _ = []
(x ∷ xs) >>=ₗ f = f x List.++ (xs >>=ₗ f)

instance
  Maybe-Monad : ∀ {a} → RawMonad {a} Maybe
  _>>=_  {{Maybe-Monad}} = _>>=ₘ_
  return {{Maybe-Monad}} = just

  List-Monad : ∀ {a} → RawMonad {a} List
  _>>=_  {{List-Monad}} = _>>=ₗ_
  return {{List-Monad}} x = x ∷ []

instance
  Maybe-Traversable : ∀ {a} → RawTraversable {a} Maybe
  traverse {{Maybe-Traversable}} f (just x) = just <$> f x
  traverse {{Maybe-Traversable}} f nothing = return nothing

  List-Traversable : ∀ {a} → RawTraversable {a} List
  traverse {{List-Traversable}} f [] = return []
  traverse {{List-Traversable}} f (x ∷ xs) =
    f x >>= λ x′ →
    traverse {{List-Traversable}} f xs >>= λ xs′ →
    return (x′ ∷ xs′)

instance
  Maybe-Choice : ∀ {a} → Choice {a} Maybe
  Choice._<|>_ Maybe-Choice (just x) _ = just x
  Choice._<|>_ Maybe-Choice nothing y = y
