
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
  open DFS _⇒_ isStrictTotalOrder
  open IsStrictTotalOrder isStrictTotalOrder using (_≟_)

  private
    module Tree = AVL isStrictTotalOrder
    open Tree using (Tree)

    pathTo⇒ : ∀ {x y} → Path x y → x ⇒ y
    pathTo⇒ (edge p) = p
    pathTo⇒ (connect ps qs) = trans (pathTo⇒ ps) (pathTo⇒ qs)

    mkGraph : Database → Graph
    mkGraph [] = Tree.empty
    mkGraph ((x , y , p) ∷ ps) = Tree.insertWith x ((y , p) ∷ []) List._++_ (mkGraph ps)

    findPath : Database → ∀ x y → Maybe (Path x y)
    findPath db x y =
      let db′ = mkGraph db
      in findDest db′ {y} (λ v → v ≟ y) x

  tryProve : Database → ∀ x y → Maybe (x ⇒ y)
  tryProve db x y = findPath db x y >>=ₘ just ∘ pathTo⇒

  findTransTargets : Database → ∀ x → List (∃ λ y → x ⇒ y)
  findTransTargets db x = allTargetsFrom (mkGraph db) x >>=ₗ λ {(y , c) → return (y , pathTo⇒ c)}
