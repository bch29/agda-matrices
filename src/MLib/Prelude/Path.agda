module MLib.Prelude.Path where

open import MLib.Prelude.FromStdlib

open import Relation.Binary using (Rel; Transitive)

data Path {v e} {V : Set v} (_⇒_ : Rel V e) (x y : V) : Set (v ⊔ˡ e) where
  edge :  (e : x ⇒ y) → Path _⇒_ x y
  connect : ∀ {z} (p₁ : Path _⇒_ x z) (p₂ : Path _⇒_ z y) → Path _⇒_ x y

transPath : ∀ {v e} {V : Set v} {_⇒_ : Rel V e} → Transitive _⇒_ → ∀ {x y} → Path _⇒_ x y → x ⇒ y
transPath trans (edge e) = e
transPath trans (connect p q) = trans (transPath trans p) (transPath trans q)
