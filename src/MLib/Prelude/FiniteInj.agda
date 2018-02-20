module MLib.Prelude.FiniteInj where

open import MLib.Prelude.FromStdlib
import MLib.Prelude.Fin as Fin
import MLib.Prelude.Fin.Pieces as P
open Fin using (Fin)

open import Data.List.All as All using (All; []; _∷_) hiding (module All)

module Table where
  open import Data.Table public
  open import Data.Table.Properties public
open Table using (Table; tabulate; lookup) hiding (module Table)

open import Function.LeftInverse using (LeftInverse; _↞_)
open import Function.Inverse using (Inverse)
open import Function.Equality as FE using (_⟶_; _⟨$⟩_; cong)
open import Function.Related using () renaming (module EquationalReasoning to RelReasoning)

open Algebra using (IdempotentCommutativeMonoid)

record IsFiniteSet {c ℓ} {A : Set c} (_≈_ : Rel A ℓ) (N : ℕ) : Set (c ⊔ˡ ℓ) where
  field
    isEquivalence : IsEquivalence _≈_

  setoid : Setoid _ _
  setoid = record { isEquivalence = isEquivalence }
  open IsEquivalence isEquivalence public

  OntoFin : ℕ → Set _
  OntoFin N = LeftInverse setoid (≡.setoid (Fin N))

  field
    ontoFin : OntoFin N

  open Table
  open List using ([]; _∷_)

  private
    enumTableAt : ∀ {N} → OntoFin N → Table A N
    enumTableAt ontoFin = tabulate (LeftInverse.from ontoFin ⟨$⟩_)

    enumerateAt : ∀ {N} → OntoFin N → List A
    enumerateAt ontoFin = Table.toList (enumTableAt ontoFin)

  enumTable : Table A N
  enumTable = enumTableAt ontoFin

  enumerate : List A
  enumerate = Table.toList enumTable

  module _ {c ℓ} (icMonoid : IdempotentCommutativeMonoid c ℓ) where
    module S = IdempotentCommutativeMonoid icMonoid
    open S using (_∙_; ∙-cong) renaming (Carrier to S; _≈_ to _≈′_)
    open import Algebra.Operations.CommutativeMonoid S.commutativeMonoid
    open import Algebra.Properties.CommutativeMonoid S.commutativeMonoid

    private
      module _ {n : ℕ} (ontoFin′ : OntoFin (Nat.suc n)) where
        from = LeftInverse.from ontoFin′ ⟨$⟩_
        to = LeftInverse.to ontoFin′ ⟨$⟩_

        enumTable′ : Table A (Nat.suc n)
        enumTable′ = enumTableAt ontoFin′

        ap : setoid ⟶ S.setoid → A → S
        ap = _⟨$⟩_

        enumTable-complete′ : ∀ (func : setoid ⟶ S.setoid) x → (func ⟨$⟩ x) ∙ sumTable (map (ap func) enumTable′) ≈′ sumTable (map (ap func) enumTable′)
        enumTable-complete′ func x =
          begin
            f x ∙ sumTable (map f enumTable′)                                         ≈⟨ ∙-cong S.refl (sumTable-permute (map f enumTable′) (Fin.swapIndices Fin.zero i)) ⟩
            f x ∙ sumTable (permute (Fin.swapIndices Fin.zero i) (map f enumTable′))  ≡⟨⟩
            f x ∙ (f (from (to x)) ∙ _)                                               ≈⟨ ∙-cong S.refl (∙-cong (cong func (LeftInverse.left-inverse-of ontoFin′ x)) S.refl) ⟩
            f x ∙ (f x ∙ _)                                                           ≈⟨ S.sym (S.assoc _ _ _) ⟩
            (f x ∙ f x) ∙ _                                                           ≈⟨ ∙-cong (S.idem _) S.refl ⟩
            f x ∙ _                                                                   ≈⟨ ∙-cong (cong func (sym (LeftInverse.left-inverse-of ontoFin′ x))) S.refl ⟩
            f (from (to x)) ∙ _                                                       ≡⟨⟩
            sumTable (permute (Fin.swapIndices Fin.zero i) (map f enumTable′))        ≈⟨ S.sym (sumTable-permute (map f enumTable′) (Fin.swapIndices Fin.zero i)) ⟩
            sumTable (map f enumTable′)                                               ∎
          where
            f = ap func
            i = to x

            open EqReasoning S.setoid

    private
      inhabited : ∀ {N} (i : Fin N) → ∃ λ n → N ≡ Nat.suc n
      inhabited Fin.zero = _ , ≡.refl
      inhabited (Fin.suc i) = _ , ≡.refl

      enumTable-complete′′ :
        ∀ {N} (ontoFin′ : OntoFin N) (f : setoid ⟶ S.setoid) x
        → (f ⟨$⟩ x) ∙ sumTable (Table.map (f ⟨$⟩_) (enumTableAt ontoFin′))
          ≈′ sumTable (Table.map (f ⟨$⟩_) (enumTableAt ontoFin′))
      enumTable-complete′′ ontoFin′ f x with inhabited (LeftInverse.to ontoFin′ ⟨$⟩ x)
      enumTable-complete′′ ontoFin′ f x | n , ≡.refl = enumTable-complete′ ontoFin′ f x

      sum/map-hom : ∀ {n} {a}{A : Set a} (f : A → S) (t : Table A n) → sum (List.map f (toList t)) ≡ sumTable (map f t)
      sum/map-hom f t =
        begin
          sum (List.map f (toList t))   ≡⟨ ≡.cong sum (Table.map-toList-hom t) ⟩
          sum (toList (map f t))        ≡⟨ ≡.sym (sumTable-toList (map f t)) ⟩
          sumTable (map f t)            ∎
        where
          open ≡.Reasoning


    -- Enumeration is complete: in any idempotent commutative monoid, adding one
    -- more element to the sum won't change it. In particular, this works in the
    -- powerset monoid, where 'f' is the singleton at its argument and addition
    -- is set union. This shows that every member of 'A' is present in the
    -- enumeration (even though the powerset monoid is quite difficult to
    -- implement in Agda so this proof is not present).

    enumTable-complete : ∀ f x → (f ⟨$⟩ x) ∙ sumTable (map (f ⟨$⟩_) enumTable) ≈′ sumTable (map (f ⟨$⟩_) enumTable)
    enumTable-complete = enumTable-complete′′ ontoFin

    enumerate-complete : ∀ (f : setoid ⟶ S.setoid) x → (f ⟨$⟩ x) ∙ sum (List.map (f ⟨$⟩_) enumerate) ≈′ sum (List.map (f ⟨$⟩_) enumerate)
    enumerate-complete func x =
      begin
        f x ∙ sum (List.map f enumerate)           ≡⟨⟩
        f x ∙ sum (List.map f (toList enumTable))  ≡⟨ ≡.cong₂ _∙_ ≡.refl (sum/map-hom f enumTable) ⟩
        f x ∙ sumTable (map f enumTable)           ≈⟨ enumTable-complete func x ⟩
        sumTable (map f enumTable)                 ≡⟨ ≡.sym (sum/map-hom f enumTable) ⟩
        sum (List.map f enumerate)                 ∎
      where
        f = func ⟨$⟩_
        open EqReasoning S.setoid

empty-isFinite : ∀ {c ℓ} {A : Set c} {_≈_ : Rel A ℓ} → ¬ A → IsFiniteSet _≈_ 0
empty-isFinite ¬A = record
  { isEquivalence = record { refl = λ {x} → ⊥-elim (¬A x) ; sym = λ {x} → ⊥-elim (¬A x) ; trans = λ {x} → ⊥-elim (¬A x) }
  ; ontoFin = record
    { to = record { _⟨$⟩_ = ⊥-elim ∘ ¬A ; cong = λ {x} → ⊥-elim (¬A x) }
    ; from = record { _⟨$⟩_ = λ () ; cong = λ {i} → ⊥-elim (nofin0 i) }
    ; left-inverse-of = ⊥-elim ∘ ¬A
    }
  }
  where
    nofin0 : ¬ Fin 0
    nofin0 ()

unitary-isFinite : ∀ {c ℓ} (setoid : Setoid c ℓ) →
  let open Setoid setoid
  in ∀ x → (∀ y → x ≈ y) → IsFiniteSet _≈_ 1
unitary-isFinite setoid x unique = record
  { isEquivalence = isEquivalence
  ; ontoFin = record
    { to = FE.const Fin.zero
    ; from = FE.const x
    ; left-inverse-of = unique
    }
  }
  where open Setoid setoid

record FiniteSet c ℓ : Set (sucˡ (c ⊔ˡ ℓ)) where
  field
    Carrier : Set c
    _≈_ : Rel Carrier ℓ
    N : ℕ
    isFiniteSet : IsFiniteSet _≈_ N

  open IsFiniteSet isFiniteSet public

record PointwiseFiniteSet {a} (A : Set a) c ℓ : Set (a ⊔ˡ sucˡ (c ⊔ˡ ℓ)) where
  field
    Carrier : A → Set c
    _≈_ : ∀ {x} → Rel (Carrier x) ℓ
    boundAt : A → ℕ
    finiteAt : ∀ x → IsFiniteSet {A = Carrier x} _≈_ (boundAt x)

  module _ x where
    open IsFiniteSet (finiteAt x) public

TableAny : ∀ {n} {a p} {A : Set a} (P : A → Set p) (t : Table A n) → Set p
TableAny P t = ∃ (P ∘ lookup t)

-- data TableAny {n} {a p} {A : Set a} (P : A → Set p) (t : Table A n) : Set (a ⊔ˡ p) where
--   index : ∀ {i} → P (lookup t i) → TableAny P t

module _ {c} {ℓ} (F : FiniteSet c ℓ) where
  open FiniteSet F

  Σₜ : ∀ {p} → (Carrier → Set p) → Set p
  Σₜ P = TableAny P enumTable

module _ {a} {A : Set a} {N} (F : IsFiniteSet {A = A} _≡_ N) where
  private
    finiteSet : FiniteSet _ _
    finiteSet = record { isFiniteSet = F }

    module F = FiniteSet finiteSet

  module _ {p} {P : A → Set p} {boundAt : A → ℕ} (finiteAt : ∀ {x} → IsFiniteSet {A = P x} _≡_ (boundAt x)) where
    private
      pwFiniteSet : PointwiseFiniteSet A _ _
      pwFiniteSet = record { finiteAt = λ x → finiteAt {x} }

      module PW = PointwiseFiniteSet pwFiniteSet

      pieces : P.Pieces A boundAt
      pieces = record
        { numPieces = N
        ; pieces = F.enumTable
        }

      open P.Pieces pieces hiding (pieces)

    Σₜ-isFiniteSet : IsFiniteSet {A = Σₜ finiteSet P} _≡_ totalSize
    Σₜ-isFiniteSet = record
      { isEquivalence = ≡.isEquivalence
      ; ontoFin =
        Σₜ finiteSet P              ∼⟨ intoCoords ⟩
        Σ (Fin N) (Fin ∘ sizeAt)    ↔⟨ P.asPiece pieces ⟩
        Fin totalSize               ∎
      }
      where
        open RelReasoning

        to : Σₜ finiteSet P → Σ (Fin N) (Fin ∘ sizeAt)
        to (_ , px) = _ , LeftInverse.to (PW.ontoFin _) ⟨$⟩ px

        from : Σ (Fin N) (Fin ∘ sizeAt) → Σₜ finiteSet P
        from (i , j) = _ , (LeftInverse.from (PW.ontoFin _) ⟨$⟩ j)

        left-inverse-of : ∀ x → from (to x) ≡ x
        left-inverse-of (i , x) = ≡.cong (i ,_) (LeftInverse.left-inverse-of (PW.ontoFin _) x)

        intoCoords : Σₜ finiteSet P ↞ Σ (Fin N) (Fin ∘ sizeAt)
        intoCoords = record
          { to = ≡.→-to-⟶ to
          ; from = ≡.→-to-⟶ from
          ; left-inverse-of = left-inverse-of
          }

module _ {a p} {A : Set a} {P : A → Set p} {boundAt : A → ℕ} (finiteAt : ∀ {x} → IsFiniteSet {A = P x} _≡_ (boundAt x)) where
  private
    pwFiniteSet : PointwiseFiniteSet A _ _
    pwFiniteSet = record { finiteAt = λ x → finiteAt {x} }

    module PW = PointwiseFiniteSet pwFiniteSet

  finiteAll : ∀ {xs : List A} → IsFiniteSet {A = All P xs} _≡_ (List.product (List.map boundAt xs))
  finiteAll = record
    { isEquivalence = ≡.isEquivalence
    ; ontoFin = record
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

      to : ∀ {xs} → All P xs → Fin (List.product (List.map boundAt xs))
      to [] = Fin.zero
      to (_∷_ {x} {xs} px ap) = joinProd ((LeftInverse.to (PW.ontoFin _) ⟨$⟩ px) , to ap)

      from : ∀ {xs} → Fin (List.product (List.map boundAt xs)) → All P xs
      from {List.[]} _ = []
      from {x List.∷ xs} i =
        (LeftInverse.from (PW.ontoFin _) ⟨$⟩ (proj₁ (splitProd i))) ∷
        from {xs} (proj₂ (splitProd {boundAt x} i))

      left-inverse-of : ∀ {xs} (ap : All P xs) → from (to ap) ≡ ap
      left-inverse-of [] = ≡.refl
      left-inverse-of (px ∷ ap)
        rewrite splitProd-joinProd ((LeftInverse.to (PW.ontoFin _) ⟨$⟩ px) , to ap)
              | LeftInverse.left-inverse-of (IsFiniteSet.ontoFin finiteAt) px
              | left-inverse-of ap
              = ≡.refl
