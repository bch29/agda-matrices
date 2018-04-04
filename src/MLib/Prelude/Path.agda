module MLib.Prelude.Path where

open import MLib.Prelude.FromStdlib

data Path {v e} {V : Set v} (_⇒_ : V → V → Set e) (x y : V) : Set (v ⊔ˡ e) where
  edge :  (e : x ⇒ y) → Path _⇒_ x y
  connect : ∀ {z} (p₁ : Path _⇒_ x z) (p₂ : Path _⇒_ z y) → Path _⇒_ x y

