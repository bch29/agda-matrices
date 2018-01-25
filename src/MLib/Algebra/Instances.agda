module MLib.Algebra.Instances where

open import MLib.Prelude
open List using ([]; _∷_)

open import Data.List.All as All using (All; _∷_; [])
open import Data.List.Any using (Any; here; there)
open import Data.List.Any.Membership.Propositional using (_∈_)

--------------------------------------------------------------------------------
--  Subset combinators
--------------------------------------------------------------------------------

_⊆_ : ∀ {a} {A : Set a} → List A → List A → Set a
_⊆_ ps qs = All (_∈ qs) ps

⊆-trans : ∀ {a} {A : Set a} {xs ys zs : List A} → xs ⊆ ys → ys ⊆ zs → xs ⊆ zs
⊆-trans [] q = []
⊆-trans (px ∷ p) q = All.lookup q px ∷ ⊆-trans p q

getAll⊆ : ∀ {a p} {A : Set a} {P : A → Set p} {xs ys : List A} → xs ⊆ ys → All P ys → All P xs
getAll⊆ [] apy = []
getAll⊆ (px ∷ s) apy = All.lookup apy px ∷ getAll⊆ s apy

it : ∀ {a} {A : Set a} ⦃ inst : A ⦄ → A
it ⦃ inst ⦄ = inst

--------------------------------------------------------------------------------
--  Instances
--------------------------------------------------------------------------------

instance
  inst-refl : ∀ {a} {A : Set a} {x : A} → x ≡ x
  inst-refl = ≡.refl

  head-here : ∀ {a p} {A : Set a} {P : A → Set p} {x : A} {xs} ⦃ px : P x ⦄ → Any P (x ∷ xs)
  head-here ⦃ px ⦄ = here px

  tail-there : ∀ {a p} {A : Set a} {P : A → Set p} {x : A} {xs} ⦃ inTail : Any P xs ⦄ → Any P (x ∷ xs)
  tail-there ⦃ inTail ⦄ = there inTail

  []-All : ∀ {a p} {A : Set a} {P : A → Set p} → All P []
  []-All = []

  ∷-All : ∀ {a p} {A : Set a} {P : A → Set p} {x xs} ⦃ px : P x ⦄ ⦃ ap : All P xs ⦄ → All P (x ∷ xs)
  ∷-All ⦃ px ⦄ ⦃ ap ⦄ = px ∷ ap


private
  module Tests {a} {A : Set a} {x y z : A} where

    l1 l2 l3 l4 l5 : List A
    l1 = x ∷ y ∷ z ∷ []
    l2 = x ∷ y ∷ []
    l3 = y ∷ z ∷ []
    l4 = x ∷ z ∷ []
    l5 = y ∷ x ∷ []

    t1 : l2 ⊆ l1
    t1 = it

    t2 : l3 ⊆ l1
    t2 = it

    t3 : l1 ⊆ l1
    t3 = it

    t4 : l4 ⊆ l1
    t4 = it

    t5 : l5 ⊆ l1
    t5 = it
