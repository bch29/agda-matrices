
open import MLib.Prelude.FromStdlib

module MLib.Prelude.TransitiveProver {a p} {A : Set a} (_⇒_ : A → A → Set p) (trans : Transitive _⇒_) where

import MLib.Prelude.DFS as DFS

open List using ([]; _∷_)

open import Relation.Nullary using (yes; no)
open import Relation.Binary using (Decidable; IsStrictTotalOrder)

import Data.AVL as AVL

Database : Set (a ⊔ˡ p)
Database = List (∃₂ λ x y → x ⇒ y)

module Search {r} {_<_ : Rel A r} (isStrictTotalOrder : IsStrictTotalOrder _≡_ _<_) where
  private
    module DFS′ = DFS _⇒_ isStrictTotalOrder
  open DFS′
  open DFS′ public using (Graph)
  open IsStrictTotalOrder isStrictTotalOrder using (_≟_)

  private
    module Tree = AVL isStrictTotalOrder
    open Tree using (Tree)

  mkGraph : Database → Graph
  mkGraph [] = Tree.empty
  mkGraph ((x , y , p) ∷ ps) = Tree.insertWith x ((y , p) ∷ []) List._++_ (mkGraph ps)

  private
    pathTo⇒ : ∀ {x y} → Path x y → x ⇒ y
    pathTo⇒ (edge p) = p
    pathTo⇒ (connect ps qs) = trans (pathTo⇒ ps) (pathTo⇒ qs)

    findPath : Graph → ∀ x y → Maybe (Path x y)
    findPath gr x y = findDest gr {y} (λ v → v ≟ y) x

  tryProve′ : Graph → ∀ x y → Maybe (x ⇒ y)
  tryProve′ gr x y = findPath gr x y >>=ₘ just ∘ pathTo⇒

  findTransTargets′ : Graph → ∀ x → List (∃ λ y → x ⇒ y)
  findTransTargets′ gr x = allTargetsFrom gr x >>=ₗ λ {(y , c) → return (y , pathTo⇒ c)}

  tryProve : Database → ∀ x y → Maybe (x ⇒ y)
  tryProve = tryProve′ ∘ mkGraph

  findTransTargets : Database → ∀ x → List (∃ λ y → x ⇒ y)
  findTransTargets = findTransTargets′ ∘ mkGraph
