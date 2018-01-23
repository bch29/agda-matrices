module MLib.Prelude.Paths where

open import MLib.Prelude.FromStdlib

open import Data.Maybe using (Maybe; just; nothing; maybe)
open import Relation.Binary.PropositionalEquality using (_→-setoid_; _≗_) public

module OverΣ where
  open import Relation.Binary.Sigma.Propositional public

open OverΣ using (OverΣ) public

module Pointwise where
  pairSetoid : ∀ {a p q} (A : Set a) (P : A → Set p) (Q : A → Set q) → Setoid _ _
  pairSetoid A P Q = OverΣ.setoid (λ x → P x →-setoid Q x)

  liftInj :
    ∀ {a a′ b} {A : Set a} {A′ : Set a′} {B : Set b}
    {k : A′ → A} → (∀ x → ∃ λ y → x ≡ k y)
    → {f g : A → B} → (f ∘ k) ≗ (g ∘ k) → f ≗ g
  liftInj k-admissible p x with k-admissible x
  liftInj k-admissible p ._ | y , ≡.refl = p y

  liftPseudoInj :
    ∀ {a a′ b} {A : Set a} {A′ : Set a′} {B : Set b}
    {k : A′ → A} {z : A} → (∀ x → x ≡ z ⊎ ∃ λ y → x ≡ k y)
    → {f g : A → B} → f z ≡ g z → (f ∘ k) ≗ (g ∘ k) → f ≗ g
  liftPseudoInj {k = k} {z} k-admissible p q = liftInj k′-admissible (maybe q p)
    where
      k′-admissible : ∀ x → ∃ λ y → x ≡ maybe k z y
      k′-admissible x with k-admissible x
      k′-admissible x | inj₁ r = nothing , r
      k′-admissible x | inj₂ (y , r) = just y , r

  liftInjOver :
    ∀ {i p a} {I : Set i} {P : I → Set p} {A : Set a}
      {h : I → I} {k : ∀ {i} → P i → P (h i)}
      {i j : I} {f : P (h i) → A} {g : P (h j) → A}
    → (∀ {i} (x : P (h i)) → ∃ λ y → x ≡ k y)
    → OverΣ (λ {x} → _≗_ {A = P x}) (i , f ∘ k) (j , g ∘ k) → OverΣ (λ {x} → _≗_ {A = P x}) (h i , f) (h j , g)
  liftInjOver k-admissible (≡.refl , p) = ≡.refl , liftInj k-admissible p

  liftPseudoInjOver :
    ∀ {i p a} {I : Set i} {P : I → Set p} {A : Set a}
      {h : I → I} {k : ∀ {i} → P i → P (h i)} {z : ∀ {i} → P (h i)}
      {i j : I} {f : P (h i) → A} {g : P (h j) → A}
    → (∀ {i} (x : P (h i)) → x ≡ z ⊎ ∃ λ y → x ≡ k y) → f z ≡ g z
    → OverΣ (λ {x} → _≗_ {A = P x}) (i , f ∘ k) (j , g ∘ k) → OverΣ (λ {x} → _≗_ {A = P x}) (h i , f) (h j , g)
  liftPseudoInjOver k-admissible p (≡.refl , q) = ≡.refl , liftPseudoInj k-admissible p q
