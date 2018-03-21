module MLib.Prelude.RelProps where

open import MLib.Prelude.FromStdlib

import Relation.Binary.Indexed as I
open import Function.Equality using (_⟶_; _⟨$⟩_; cong)
open import Function.Inverse using (Inverse; _↔_)
open import Function.LeftInverse using (LeftInverse; _↞_)
import Data.Product.Relation.SigmaPropositional as OverΣ
import Data.Product.Relation.Pointwise.Dependent as ΣR

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


Σ-↞′ :
  ∀ {a a′ b β} {A : Set a} {A′ : Set a′} {B-setoid : A → Setoid b β} (f : A ↞ A′)
  → LeftInverse (OverΣ.setoid B-setoid) (OverΣ.setoid (B-setoid ∘ (LeftInverse.from f ⟨$⟩_)))
Σ-↞′ {A = A} {A′} {B-setoid} f = record
  { to = record
    { _⟨$⟩_ = uncurry λ x y → LeftInverse.to f ⟨$⟩ x , ≡.subst B (≡.sym (LeftInverse.left-inverse-of f _)) y
    ; cong = uncurry λ {≡.refl y → ≡.refl , subst≈ _ _ (≡.sym (LeftInverse.left-inverse-of f _)) y}
    }
  ; from = record
    { _⟨$⟩_ = uncurry λ x y → LeftInverse.from f ⟨$⟩ x , y
    ; cong = λ { (≡.refl , q) → ≡.refl , q }
    }
  ; left-inverse-of = uncurry λ x y → OverΣ.symmetric sym (OverΣ.subst (≡.sym (LeftInverse.left-inverse-of f _)) refl)
  }
  where
    module B x = Setoid (B-setoid x)
    module B′ {x} = Setoid (B-setoid x)
    open B using () renaming (Carrier to B)
    open B′

    subst≈ : ∀ {i j} (x y : B i) (p : i ≡ j) → x ≈ y → ≡.subst B p x ≈ ≡.subst B p y
    subst≈ x y ≡.refl q = q
