module MLib.Prelude.RelProps where

open import MLib.Prelude.FromStdlib

open import Function.Equality using (_⟶_; _⟨$⟩_; cong)
open import Function.Inverse using (Inverse; _↔_)
open import Function.LeftInverse using (LeftInverse; _↞_)
import Data.Product.Relation.SigmaPropositional as OverΣ

Σ-bij : ∀ {a b c} {A : Set a} {B : A → Set b} {C : A → Set c} → (∀ x → B x ↔ C x) → Σ A B ↔ Σ A C
Σ-bij pw = record
  { to = ≡.→-to-⟶ (uncurry λ x y → x , Inverse.to (pw x) ⟨$⟩ y)
  ; from = ≡.→-to-⟶ (uncurry λ x y → x , Inverse.from (pw x) ⟨$⟩ y)
  ; inverse-of = record
    { left-inverse-of = uncurry λ x y → OverΣ.to-≡ (≡.refl , Inverse.left-inverse-of (pw x) y)
    ; right-inverse-of = uncurry λ x y → OverΣ.to-≡ (≡.refl , Inverse.right-inverse-of (pw x) y)
    }
  }


Σ-↞ : ∀ {a b c} {A : Set a} {B : A → Set b} {C : A → Set c} → (∀ x → B x ↞ C x) → Σ A B ↞ Σ A C
Σ-↞ f = record
  { to = ≡.→-to-⟶ (uncurry λ x y → x , LeftInverse.to (f x) ⟨$⟩ y)
  ; from = ≡.→-to-⟶ (uncurry λ x y → x , LeftInverse.from (f x) ⟨$⟩ y)
  ; left-inverse-of = uncurry λ x y → OverΣ.to-≡ (≡.refl , LeftInverse.left-inverse-of (f x) y)
  }


Σ-↞′ : ∀ {a a′ b} {A : Set a} {A′ : Set a′} {B : A → Set b} (f : A ↞ A′) → Σ A B ↞ Σ A′ (B ∘ (LeftInverse.from f ⟨$⟩_))
Σ-↞′ {B = B} f = record
  { to = ≡.→-to-⟶ (uncurry λ x y → LeftInverse.to f ⟨$⟩ x , ≡.subst B (≡.sym (LeftInverse.left-inverse-of f _)) y)
  ; from = ≡.→-to-⟶ (uncurry λ x y → _ , y)
  ; left-inverse-of = uncurry λ x y →
    OverΣ.to-≡ (OverΣ.symmetric ≡.sym (OverΣ.subst (≡.sym (LeftInverse.left-inverse-of f _)) ≡.refl))
  }
