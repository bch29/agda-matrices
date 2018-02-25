module MLib.Prelude.Finite where

open import MLib.Prelude.FromStdlib
import MLib.Prelude.Fin as Fin
import MLib.Prelude.Fin.Pieces as P
open import MLib.Prelude.RelProps
open Fin using (Fin)

open import Data.List.All as All using (All; []; _∷_) hiding (module All)
open import Data.List.Any as Any using (Any; here; there) hiding (module Any)
import Data.List.Any.Membership as Membership
import Data.List.Any.Membership.Propositional as PropMembership

module Table where
  open import Data.Table public
  open import Data.Table.Properties public
open Table using (Table; tabulate; lookup) hiding (module Table)

open import Function.LeftInverse using (LeftInverse; _↞_) renaming (_∘_ to _ⁱ∘_)
open import Function.Inverse using (Inverse; _↔_)
open import Function.Equality as FE using (_⟶_; _⟨$⟩_; cong)
open import Function.Related using () renaming (module EquationalReasoning to RelReasoning)

open Algebra using (IdempotentCommutativeMonoid)

--------------------------------------------------------------------------------
--  Main Definition
--------------------------------------------------------------------------------

record IsFiniteSetoid {c ℓ} (setoid : Setoid c ℓ) (N : ℕ) : Set (c ⊔ˡ ℓ) where
  open Setoid setoid public
  open Setoid setoid using () renaming (Carrier to A)

  OntoFin : ℕ → Set _
  OntoFin N = LeftInverse setoid (≡.setoid (Fin N))

  field
    ontoFin : OntoFin N

  fromIx : Fin N → A
  fromIx i = LeftInverse.from ontoFin ⟨$⟩ i

  toIx : A → Fin N
  toIx x = LeftInverse.to ontoFin ⟨$⟩ x

  fromIx-toIx : ∀ x → fromIx (toIx x) ≈ x
  fromIx-toIx = LeftInverse.left-inverse-of ontoFin

  enumTable : Table A N
  enumTable = tabulate fromIx

  enumerate : List A
  enumerate = Table.toList enumTable


IsFiniteSet : ∀ {a} → Set a → ℕ → Set a
IsFiniteSet = IsFiniteSetoid ∘ ≡.setoid


record FiniteSet c ℓ : Set (sucˡ (c ⊔ˡ ℓ)) where
  field
    setoid : Setoid c ℓ
    N : ℕ
    isFiniteSetoid : IsFiniteSetoid setoid N

  open IsFiniteSetoid isFiniteSetoid public

--------------------------------------------------------------------------------
--  Combinators
--------------------------------------------------------------------------------

-- An enumerable setoid is finite

module _ {c ℓ} (setoid : Setoid c ℓ) where
  open Setoid setoid
  open Membership setoid

  Any-cong : ∀ {xs} → (∀ x → x ∈ xs) → Set _
  Any-cong f = ∀ {x y} → x ≈ y → Any.index (f x) ≡ Any.index (f y)

  private
    from : ∀ xs → Fin (List.length xs) → Carrier
    from List.[] ()
    from (x List.∷ xs) Fin.zero = x
    from (x List.∷ xs) (Fin.suc i) = from xs i

    left-inverse-of : ∀ {xs} (f : ∀ x → x ∈ xs) x → from xs (Any.index (f x)) ≈ x
    left-inverse-of f x = go (f x)
      where
      go : ∀ {xs} (p : x ∈ xs) → from xs (Any.index p) ≈ x
      go (here px) = sym px
      go (there p) = go p

  enumerable-isFiniteSetoid : ∀ {xs} (f : ∀ x → x ∈ xs) → Any-cong f → IsFiniteSetoid setoid (List.length xs)
  enumerable-isFiniteSetoid {xs} f f-cong = record
    { ontoFin = record
      { to = record
        { _⟨$⟩_ = Any.index ∘ f
        ; cong = f-cong
        }
      ; from = ≡.→-to-⟶ (from xs)
      ; left-inverse-of = left-inverse-of f
      }
    }


-- As a special case of the previous theorem requiring fewer conditions, an
-- enumerable set is finite.

module _ {a} {A : Set a} where
  open PropMembership

  enumerable-isFiniteSet : (xs : List A) (f : ∀ x → x ∈ xs) → IsFiniteSet A (List.length xs)
  enumerable-isFiniteSet _ f = enumerable-isFiniteSetoid (≡.setoid _) f (≡.cong (Any.index ∘ f))


-- Given a function with a left inverse from some 'A' to a finite set, 'A' must also be finite.

extendFinite : ∀ {c ℓ c′ ℓ′} {S : Setoid c ℓ} (F : FiniteSet c′ ℓ′) → LeftInverse S (FiniteSet.setoid F) → IsFiniteSetoid S (FiniteSet.N F)
extendFinite finiteSet ontoF = record
  { ontoFin = ontoFin ⁱ∘ ontoF
  }
  where
    open FiniteSet finiteSet using (ontoFin)


-- Given a family of finite sets, indexed by a finite set, the sum over the entire family is finite.

module _ {a} {A : Set a} {N} (F : IsFiniteSetoid (≡.setoid A) N) where
  private
    finiteSet : FiniteSet _ _
    finiteSet = record { isFiniteSetoid = F }

    module F = FiniteSet finiteSet

    Σᶠ : ∀ {p} → (A → Set p) → Set p
    Σᶠ P = ∃ (P ∘ lookup F.enumTable)

  module _ {p} {P : A → Set p} {boundAt : A → ℕ} (finiteAt : ∀ x → IsFiniteSet (P x) (boundAt x)) where
    private
      module PW x = IsFiniteSetoid (finiteAt x)

      pieces : P.Pieces A boundAt
      pieces = record
        { numPieces = N
        ; pieces = F.enumTable
        }

      open P.Pieces pieces hiding (pieces)

    Σ-isFiniteSet : IsFiniteSet (Σ A P) totalSize
    Σ-isFiniteSet = record
      { ontoFin =
        ∃ P                         ∼⟨ Σ-↞′ F.ontoFin ⟩
        Σᶠ P                        ∼⟨ intoCoords ⟩
        Σ (Fin N) (Fin ∘ sizeAt)    ↔⟨ P.asPiece pieces ⟩
        Fin totalSize               ∎
      }
      where
        open RelReasoning

        to : Σᶠ P → Σ (Fin N) (Fin ∘ sizeAt)
        to (_ , px) = _ , PW.toIx _ px

        from : Σ (Fin N) (Fin ∘ sizeAt) → Σᶠ P
        from (i , j) = _ , PW.fromIx _ j

        left-inverse-of : ∀ x → from (to x) ≡ x
        left-inverse-of (i , x) = ≡.cong (i ,_) (PW.fromIx-toIx _ _)

        intoCoords : Σᶠ P ↞ Σ (Fin N) (Fin ∘ sizeAt)
        intoCoords = record
          { to = ≡.→-to-⟶ to
          ; from = ≡.→-to-⟶ from
          ; left-inverse-of = left-inverse-of
          }


-- TODO: Recast as an instance of Σ-isFiniteSet

module _ {a p} {A : Set a} {P : A → Set p} (boundAt : A → ℕ) (finiteAt : ∀ x → IsFiniteSet (P x) (boundAt x)) where
  private
    module PW x = IsFiniteSetoid (finiteAt x)

  finiteAllSize : List A → ℕ
  finiteAllSize = List.product ∘ List.map boundAt


  finiteAll : (xs : List A) → IsFiniteSet (All P xs) _
  finiteAll _ = record
    { ontoFin = record
      { to = ≡.→-to-⟶ to
      ; from = ≡.→-to-⟶ from
      ; left-inverse-of = left-inverse-of
      }
    }
    where
      prodIsSum : ∀ m n → m Nat.* n ≡ Table.foldr Nat._+_ 0 (Table.replicate {m} n)
      prodIsSum ℕ.zero _ = ≡.refl
      prodIsSum (ℕ.suc m) n = ≡.cong₂ Nat._+_ (≡.refl {x = n}) (prodIsSum m n)

      splitProd : ∀ {m n} → Fin (m Nat.* n) → Fin m × Fin n
      splitProd {m} {n} ij rewrite prodIsSum m n = Inverse.from (P.asPiece (P.constPieces m n )) ⟨$⟩ ij

      joinProd : ∀ {m n} → Fin m × Fin n → Fin (m Nat.* n)
      joinProd {m} {n} ij with Inverse.to (P.asPiece (P.constPieces m n )) ⟨$⟩ ij
      joinProd {m} {n} ij | f rewrite prodIsSum m n = f

      splitProd-joinProd : ∀ {m n} (ij : Fin m × Fin n) → splitProd (joinProd ij) ≡ ij
      splitProd-joinProd {m} {n} ij rewrite prodIsSum m n = Inverse.left-inverse-of (P.asPiece (P.constPieces m n)) ij

      to : ∀ {xs} → All P xs → Fin (finiteAllSize xs)
      to [] = Fin.zero
      to (_∷_ {x} {xs} px ap) = joinProd (PW.toIx _ px , to ap)

      from : ∀ {xs} → Fin (finiteAllSize xs) → All P xs
      from {List.[]} _ = []
      from {x List.∷ xs} i =
        (PW.fromIx _ (proj₁ (splitProd i))) ∷
        from {xs} (proj₂ (splitProd {boundAt x} i))

      left-inverse-of : ∀ {xs} (ap : All P xs) → from (to ap) ≡ ap
      left-inverse-of [] = ≡.refl
      left-inverse-of (px ∷ ap)
        rewrite splitProd-joinProd (PW.toIx _ px , to ap)
              | PW.fromIx-toIx _ px
              | left-inverse-of ap
              = ≡.refl
