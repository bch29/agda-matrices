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
open Bool using (Bool; true; false) hiding (module Bool) public

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
open Table using (Table; tabulate; lookup) hiding (module Table) public

--------------------------------------------------------------------------------
--  Combinators
--------------------------------------------------------------------------------

module Function where
  open import Function public
open Function using (id; _∘_) public

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
