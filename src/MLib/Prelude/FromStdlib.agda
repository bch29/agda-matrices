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

module Nat where
  open import Data.Nat public
  open import Data.Nat.Properties public
open Nat using (ℕ) public

open import Data.Product public
  using (Σ; _×_; _,_; proj₁; proj₂; ∃; ∃₂; curry; uncurry)
open import Data.Sum public
  using (_⊎_; inj₁; inj₂)
open import Data.Maybe public
  using (Maybe; just; nothing; maybe)
open import Data.Bool public
  using (Bool; true; false; if_then_else_; _∧_; _∨_)
open import Data.Unit public
  using (⊤; tt)
open import Data.Empty public
  using (⊥; ⊥-elim)

--------------------------------------------------------------------------------
--  Combinators
--------------------------------------------------------------------------------

open import Function public
  using (id; _∘_)

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
