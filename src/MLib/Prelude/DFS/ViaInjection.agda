open import MLib.Prelude.FromStdlib
open import Relation.Binary using (Rel; _Respects₂_; IsStrictTotalOrder)
open import Function.LeftInverse using (LeftInverse; _↞_)
open import Function.Equality using (Π)

module MLib.Prelude.DFS.ViaInjection
  {v v′ e}
  (V-setoid : Setoid v v′)
  (E : Rel (Setoid.Carrier V-setoid) e)
  (E-subst : E Respects₂ (Setoid._≈_ V-setoid))
  {i p} {I : Set i}
  {_<_ : I → I → Set p} (isStrictTotalOrder : IsStrictTotalOrder _≡_ _<_)
  (injection : LeftInverse V-setoid (≡.setoid I))
  where

open import MLib.Prelude.Path
import MLib.Prelude.DFS as DFS
import Data.AVL isStrictTotalOrder as Tree

module V = Setoid V-setoid
open V using (_≈_) renaming (Carrier to V)

open Π (LeftInverse.to injection) hiding (cong) renaming (_⟨$⟩_ to toIx)
open Π (LeftInverse.from injection) hiding (cong) renaming (_⟨$⟩_ to fromIx)
open LeftInverse using (left-inverse-of)

_⇒_ : I → I → Set e
i ⇒ j = E (fromIx i) (fromIx j)

module BaseDFS = DFS _⇒_ isStrictTotalOrder
open BaseDFS public using (Graph)
open Tree using (Tree)

convertPath : ∀ {i j} → Path _⇒_ i j → Path E (fromIx i) (fromIx j)
convertPath (edge e) = edge e
convertPath (connect p₁ p₂) = connect (convertPath p₁) (convertPath p₂)

PathE-subst : ∀ {x x′ y y′} → x ≈ x′ → y ≈ y′ → Path E x y → Path E x′ y′
PathE-subst x≈x′ y≈y′ (edge e) = edge (proj₂ E-subst x≈x′ (proj₁ E-subst y≈y′ e))
PathE-subst x≈x′ y≈y′ (connect p₁ p₂) = connect (PathE-subst x≈x′ V.refl p₁) (PathE-subst V.refl y≈y′ p₂)

mkGraph : List (∃₂ E) → Graph
mkGraph = List.foldr step Tree.empty
  where
  step : ∃₂ E → Graph → Graph
  step (x , y , e) =
    let e′ = proj₂ E-subst (V.sym (left-inverse-of injection x)) (proj₁ E-subst (V.sym (left-inverse-of injection y)) e)
    in Tree.insertWith (toIx x) ((toIx y , e′) ∷ []) List._++_

allTargetsFrom : Graph → (source : V) → List (∃ (Path E source))
allTargetsFrom graph source =
  let resI = BaseDFS.allTargetsFrom graph (toIx source)
  in List.map (uncurry (λ _ p → _ , PathE-subst (left-inverse-of injection _) V.refl (convertPath p))) resI

findDest : Graph → ∀ {dest} (isDest : ∀ i → Dec (i ≡ toIx dest)) (source : V) → Maybe (Path E source dest)
findDest graph {dest} isDest source =
  let resI = BaseDFS.findDest graph isDest (toIx source)
  in Maybe.map (PathE-subst (left-inverse-of injection _) (left-inverse-of injection _) ∘ convertPath) resI
