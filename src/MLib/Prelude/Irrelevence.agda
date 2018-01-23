module MLib.Prelude.Irrelevence where

open import MLib.Prelude.FromStdlib
open import MLib.Prelude.Paths

module _ {a p b} {A : Set a} {P : A → Set p} {B : Set b} where
  IrrelevantArg : (∀ x → P x → B) → Set (a ⊔ˡ p ⊔ˡ b)
  IrrelevantArg f = ∀ {x y r s} → x ≡ y → f x r ≡ f y s

  Contractible→IrrelevantArg : (∀ {x y} (p : x ≡ y) (r : P x) (s : P y) → PathOver _≡_ p r s) → (f : ∀ x → P x → B) → IrrelevantArg f
  Contractible→IrrelevantArg contractible f {r = r} {s} ≡.refl with contractible ≡.refl r s
  Contractible→IrrelevantArg contractible f ≡.refl | ≡.refl = ≡.refl

  module Reasoning (f : ∀ x → P x → B) where
    -- infix 3 _∎
    infixr 2 chainTrans
    infix 1 begin_

    data Chain : A → A → Set (a ⊔ˡ p ⊔ˡ b) where
      chain : ∀ {x y} {r : P x} {s : P y} → f x r ≡ f y s → Chain x y

    theR : ∀ {x y} → Chain x y → P x
    theR (chain {r = r} _) = r

    theS : ∀ {x y} → Chain x y → P y
    theS (chain {s = s} _) = s

    begin_ : ∀ {x y} (ch : Chain x y) → f x (theR ch) ≡ f y (theS ch)
    begin (chain p) = p

    chainTrans : ∀ {x y z t} (prev : Chain x y) → f y (theS prev) ≡ f z t → Chain x z
    chainTrans (chain p) q = chain (≡.trans p q)

    syntax chainTrans {x} ch q = x ≡ⁱ⟨ q ⟩ ch

    -- _∎ : ∀ x → Chain x x
    -- _ ∎ = chain ≡.refl
