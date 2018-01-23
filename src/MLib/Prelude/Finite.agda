module MLib.Prelude.Finite where

open import MLib.Prelude.FromStdlib
import MLib.Prelude.Fin as Fin
open Fin using (Fin)

open Algebra using (Monoid)

import Data.List as List
import Data.List.Any.Membership as Membership

module _ {c p} (setoid : Setoid c p) where
  module S = Setoid setoid
  open S using (_≈_) renaming (Carrier to S)
  open List

  data _⊜_ : (xs ys : List S) → Set p where
    []-cong : [] ⊜ []
    ∷-cong : ∀ {x y xs ys} → x ≈ y → xs ⊜ ys → (x ∷ xs) ⊜ (y ∷ ys)

  module Props where
    refl : Reflexive _⊜_
    refl {[]} = []-cong
    refl {x ∷ xs} = ∷-cong S.refl refl

    sym : Symmetric _⊜_
    sym []-cong = []-cong
    sym (∷-cong p q) = ∷-cong (S.sym p) (sym q)

    trans : Transitive _⊜_
    trans []-cong []-cong = []-cong
    trans (∷-cong p₁ p₂) (∷-cong q₁ q₂) = ∷-cong (S.trans p₁ q₁) (trans p₂ q₂)

    isEquivalence : IsEquivalence _⊜_
    isEquivalence = record
      { refl = refl
      ; sym = sym
      ; trans = trans
      }

    assoc : ∀ xs ys zs → ((xs ++ ys) ++ zs) ⊜ (xs ++ (ys ++ zs))
    assoc [] ys zs = refl
    assoc (x ∷ xs) ys zs = ∷-cong S.refl (assoc xs ys zs)

    ∙-cong : ∀ {xs xs′ ys ys′} → xs ⊜ xs′ → ys ⊜ ys′ → (xs ++ ys) ⊜ (xs′ ++ ys′)
    ∙-cong []-cong q = q
    ∙-cong (∷-cong p q) r = ∷-cong p (∙-cong q r)

    rightId : ∀ xs → (xs ++ []) ⊜ xs
    rightId [] = []-cong
    rightId (x ∷ xs) = ∷-cong S.refl (rightId xs)

  List-monoid : Monoid c p
  List-monoid = record
    { Carrier = List S
    ; _≈_ = _⊜_
    ; _∙_ = _++_
    ; ε = List.[]
    ; isMonoid = record
      { isSemigroup = record { Props }
      ; identity = (λ _ → Props.refl) , Props.rightId
      }
    }

module MonoidOps {c p} (monoid : Monoid c p) where
  open Monoid monoid renaming (Carrier to M)

  module _ {ℓ} (F : Set ℓ) where
    Enumerate : Set (ℓ ⊔ˡ c)
    Enumerate = (F → M) → M

record Finite {c p} (F-setoid : Setoid c p) : Set (sucˡ (c ⊔ˡ p)) where
  open Setoid F-setoid renaming (Carrier to F)
  open Membership F-setoid
  open MonoidOps
  open List

  field
    enumerate : (monoid : Monoid c p) → Enumerate monoid F
    enum-exhaustive : ∀ {x} → x ∈ enumerate (List-monoid F-setoid) [_]
    enum-unique : ∀ {x} → (p q : x ∈ enumerate (List-monoid F-setoid) [_]) → p ≡ q

module _ {n : ℕ} where
  open Membership (≡.setoid (Fin n))
  open List

  private
    module _ (monoid : Monoid zeroˡ zeroˡ) where
      open Monoid monoid renaming (Carrier to M)

      enumerate : MonoidOps.Enumerate monoid (Fin n)
      enumerate = Fin.foldMap ε _∙_

    enum-exhaustive : ∀ {i} → i ∈ enumerate (List-monoid (≡.setoid (Fin n))) [_]
    enum-exhaustive {Fin.zero} = {!!}
    enum-exhaustive {Fin.suc i} = {!!}

    enum-unique : ∀ {x} → (p q : x ∈ enumerate (List-monoid (≡.setoid (Fin n))) [_]) → p ≡ q
    enum-unique p q = {!!}

  Fin-Finite : Finite (≡.setoid (Fin n))
  Fin-Finite = record { enumerate = enumerate ; enum-exhaustive = {!!} ; enum-unique = {!!} }
