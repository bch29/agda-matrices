module MLib.Finite where

open import MLib.Prelude
import MLib.Fin.Pieces as P
open import MLib.Prelude.RelProps

open import Data.List.All as All using (All; []; _∷_) hiding (module All)
open import Data.List.Any as Any using (Any; here; there) hiding (module Any)
import Data.List.Membership.Setoid as Membership
import Data.List.Membership.Propositional as PropMembership

import Relation.Binary.Indexed as I
import Relation.Unary as U using (Decidable)
open LeftInverse using () renaming (_∘_ to _ⁱ∘_)
open FE using (_⇨_; cong)
open import Function.Related using () renaming (module EquationalReasoning to RelReasoning)

import Data.Product.Relation.SigmaPropositional as OverΣ

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

  enumₜ : Table A N
  enumₜ = tabulate fromIx

  enumₗ : List A
  enumₗ = Table.toList enumₜ


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

extendedIsFinite : ∀ {c ℓ c′ ℓ′} {S : Setoid c ℓ} (F : FiniteSet c′ ℓ′) → LeftInverse S (FiniteSet.setoid F) → IsFiniteSetoid S (FiniteSet.N F)
extendedIsFinite finiteSet ontoF = record
  { ontoFin = ontoFin ⁱ∘ ontoF
  }
  where
    open FiniteSet finiteSet using (ontoFin)

extendFinite : ∀ {c ℓ c′ ℓ′} {S : Setoid c ℓ} (F : FiniteSet c′ ℓ′) → LeftInverse S (FiniteSet.setoid F) → FiniteSet c ℓ
extendFinite finiteSet ontoF = record
  { isFiniteSetoid = extendedIsFinite finiteSet ontoF
  }

module _ {c ℓ c′ ℓ′} {S : Setoid c ℓ} (F : FiniteSet c′ ℓ′) where

  extendedIsFinite′N : (¬ Setoid.Carrier S) ⊎ LeftInverse S (FiniteSet.setoid F) → ℕ
  extendedIsFinite′N (inj₁ x) = 0
  extendedIsFinite′N (inj₂ y) = FiniteSet.N F

  extendedIsFinite′ : (inj : (¬ Setoid.Carrier S) ⊎ LeftInverse S (FiniteSet.setoid F)) → IsFiniteSetoid S (extendedIsFinite′N inj)
  extendedIsFinite′ (inj₂ f) = extendedIsFinite F f
  extendedIsFinite′ (inj₁ p) = record
    { ontoFin = record
      { to = record { _⟨$⟩_ = ⊥-elim ∘ p ; cong = λ {i} → ⊥-elim (p i) }
      ; from = ≡.→-to-⟶ λ ()
      ; left-inverse-of = ⊥-elim ∘ p
      }
    }


-- Given a family of finite sets, indexed by a finite set, the sum over the entire family is finite.

module _ {c} {A : Set c} {N} (isFiniteSet : IsFiniteSet A N) where
  private
    finiteSet : FiniteSet c c
    finiteSet = record { isFiniteSetoid = isFiniteSet }
    module F = FiniteSet finiteSet

    Σᶠ : ∀ {p} → (A → Set p) → Set p
    Σᶠ P = ∃ (P ∘ lookup F.enumₜ)

  module _ {p ℓ} (finiteAt : A → FiniteSet p ℓ) where
    private
      module PW x = FiniteSet (finiteAt x)
      open PW using () renaming (Carrier to P)

      pieces : P.Pieces A PW.N
      pieces = record
        { numPieces = N
        ; pieces = F.enumₜ
        }

      open P.Pieces′ pieces hiding (pieces)

    Σ-isFiniteSetoid : IsFiniteSetoid (OverΣ.setoid PW.setoid) totalSize
    Σ-isFiniteSetoid = record
      { ontoFin
        =  Inverse.left-inverse asPiece
        ⁱ∘ intoCoords
        ⁱ∘ Σ-↞′ {B-setoid = PW.setoid} F.ontoFin
      }
      where
        P-setoidᶠ : Fin N → Setoid _ _
        P-setoidᶠ i = record
          { Carrier = P (F.fromIx i)
          ; _≈_ = PW._≈_ _
          ; isEquivalence = record
            { refl = PW.refl _
            ; sym = PW.sym _
            ; trans = PW.trans _
            }
          }

        ΣᶠP-setoid = OverΣ.setoid P-setoidᶠ

        open Setoid ΣᶠP-setoid using ()
          renaming (_≈_ to _≈ᶠ_)

        to : Σᶠ P → Σ (Fin N) (Fin ∘ sizeAt)
        to (_ , px) = _ , PW.toIx _ px

        to-cong : ∀ {x y} → x ≈ᶠ y → to x ≡ to y
        to-cong (≡.refl , q) = OverΣ.to-≡ (≡.refl , cong (LeftInverse.to (PW.ontoFin _)) q)

        from : Σ (Fin N) (Fin ∘ sizeAt) → Σᶠ P
        from (i , j) = _ , PW.fromIx _ j

        left-inverse-of : ∀ x → from (to x) ≈ᶠ x
        left-inverse-of (i , x) = ≡.refl , PW.fromIx-toIx _ _

        intoCoords : LeftInverse ΣᶠP-setoid (≡.setoid (Σ (Fin N) (Fin ∘ sizeAt)))
        intoCoords = record
          { to = record { _⟨$⟩_ = to ; cong = to-cong }
          ; from = ≡.→-to-⟶ from
          ; left-inverse-of = left-inverse-of
          }

    Σ-finiteSet : FiniteSet _ _
    Σ-finiteSet = record { isFiniteSetoid = Σ-isFiniteSetoid }

module All′ {a} {A : Set a} where
  module _ {p ℓ} (setoid : A → Setoid p ℓ) where
    module P′ x = Setoid (setoid x)
    module P′′ {x} = P′ x
    open P′ using () renaming (Carrier to P)
    open P′′ using (_≈_)

    data PW : {xs : List A} → All P xs → All P xs → Set (p ⊔ˡ ℓ) where
      [] : PW [] []
      _∷_ : ∀ {x xs} {px py : P x} {apx apy : All P xs} → px ≈ py → PW apx apy → PW (px ∷ apx) (py ∷ apy)

    PW-setoid : List A → Setoid _ _
    Setoid.Carrier (PW-setoid xs) = All P xs
    Setoid._≈_ (PW-setoid xs) = PW
    IsEquivalence.refl (Setoid.isEquivalence (PW-setoid .[])) {[]} = []
    IsEquivalence.refl (Setoid.isEquivalence (PW-setoid .(_ ∷ _))) {px ∷ ap} =
      P′′.refl ∷ IsEquivalence.refl (Setoid.isEquivalence (PW-setoid _))
    IsEquivalence.sym (Setoid.isEquivalence (PW-setoid .[])) [] = []
    IsEquivalence.sym (Setoid.isEquivalence (PW-setoid .(_ ∷ _))) (p ∷ q) =
      P′′.sym p ∷ IsEquivalence.sym (Setoid.isEquivalence (PW-setoid _)) q
    IsEquivalence.trans (Setoid.isEquivalence (PW-setoid .[])) [] [] = []
    IsEquivalence.trans (Setoid.isEquivalence (PW-setoid .(_ ∷ _))) (p ∷ q) (p′ ∷ q′) =
      P′′.trans p p′ ∷ IsEquivalence.trans (Setoid.isEquivalence (PW-setoid _)) q q′


  module _ {p} (P : A → Set p) where
    PW-≡ : ∀ {xs} {apx apy : All P xs} → PW (≡.setoid ∘ P) apx apy → apx ≡ apy
    PW-≡ [] = ≡.refl
    PW-≡ (p ∷ q) = ≡.cong₂ _∷_ p (PW-≡ q)

-- module _ {c ℓ} (finiteSet : FiniteSet c ℓ) where
--   private
--     module A = FiniteSet finiteSet

--   open A using (_≈_) renaming (Carrier to A)

--   open IsFiniteSetoid
--   open LeftInverse

--   private
--     boolToFin : Bool → Fin 2
--     boolToFin false = Fin.zero
--     boolToFin true = Fin.suc Fin.zero

--     open Nat using (_^_; _+_; _*_)

--     _ℕ+_ : ∀ {n} (m : ℕ) → Fin n → Fin (m + n)
--     zero ℕ+ i = i
--     suc m ℕ+ i = Fin.suc (m ℕ+ i)

--     -- ℕ*-+ m "i" "k" = "i + m * k"
--     ℕ*-+′ : ∀ {n} (m : ℕ) → Fin m → Fin n → Fin (n * m)
--     ℕ*-+′ {zero} m i ()
--     ℕ*-+′ {suc n} m i Fin.zero = Fin.inject+ (n * m) i
--     ℕ*-+′ {suc n} m i (Fin.suc k) = m ℕ+ (ℕ*-+′ m i k)

--     -- ℕ*-+ m "i" "k" = "i + m * k"
--     ℕ*-+ : ∀ {n} m → Fin m → Fin n → Fin (m * n)
--     ℕ*-+ m i k = ≡.subst Fin (Nat.*-comm _ m) (ℕ*-+′ m i k)

--     from-n-ary : ∀ {n m} → Table (Fin n) m → Fin (n ^ m)
--     from-n-ary {m = zero} _ = Fin.zero -- an empty table represents an empty n-ary string
--     from-n-ary {n} {suc m} t = ℕ*-+ n (Table.lookup t Fin.zero) (from-n-ary (Table.tail t))

--     from-n-ary-cong : ∀ {n m} (t t′ : Table (Fin n) m) → t Table.≗ t′ → from-n-ary t ≡ from-n-ary t′
--     from-n-ary-cong {m = zero} t t′ eq = ≡.refl
--     from-n-ary-cong {n} {suc m} t t′ eq = ≡.cong₂ (ℕ*-+ n) (eq Fin.zero) (from-n-ary-cong (Table.tail t) (Table.tail t′) (eq ∘ Fin.suc))

--     -- div-rem m i = "i % m" , "i / m"
--     div-rem : ∀ {n} m → Fin (m * n) → Fin m × Fin n
--     div-rem zero ()
--     div-rem {zero} (suc m) i with ≡.subst Fin (Nat.*-zeroʳ m) i
--     div-rem {zero} (suc m) i | ()
--     div-rem {suc n} (suc m) Fin.zero = Fin.zero , Fin.zero
--     div-rem {suc n} (suc m) (Fin.suc i) = {!!}

--     to-n-ary : ∀ {n m} → Fin (n ^ m) → Table (Fin n) m
--     to-n-ary {m = zero} _ = tabulate λ ()
--     to-n-ary {n} {suc m} k =
--       let r , d = div-rem n k
--           ind = to-n-ary {n} {m} d
--       in tabulate λ
--          { Fin.zero → r
--          ; (Fin.suc i) → lookup ind i
--          }

--   boolF-isFiniteSetoid : IsFiniteSetoid (A.setoid ⇨ ≡.setoid Bool) (2 Nat.^ A.N)
--   _⟨$⟩_ (to (ontoFin boolF-isFiniteSetoid)) f =
--     let digits = Table.map (boolToFin ∘ (f ⟨$⟩_)) A.enumₜ
--     in from-n-ary digits
--   cong (to (ontoFin boolF-isFiniteSetoid)) {f} {f′} p =
--     let t = Table.map (boolToFin ∘ (f ⟨$⟩_)) A.enumₜ
--     in from-n-ary-cong t _ λ _ → ≡.cong boolToFin (p A.refl)
--   _⟨$⟩_ (_⟨$⟩_ (from (ontoFin boolF-isFiniteSetoid)) i) x = {!!}
--   cong (_⟨$⟩_ (from (ontoFin boolF-isFiniteSetoid)) i) = {!!}
--   cong (from (ontoFin boolF-isFiniteSetoid)) ≡.refl = {!≡.cong ?!}
--   left-inverse-of (ontoFin boolF-isFiniteSetoid) = {!!}

-- module _ {c₁ ℓ₁ c₂ ℓ₂} (A-finiteSet : FiniteSet c₁ ℓ₁) (B-finiteSet : FiniteSet c₂ ℓ₂) where
--   private
--     module A = FiniteSet A-finiteSet
--     module B = FiniteSet B-finiteSet

--   open A using (_≈_) renaming (Carrier to A)
--   open B using () renaming (Carrier to B; _≈_ to _≈′_)

--   open IsFiniteSetoid
--   open LeftInverse

--   function-isFiniteSetoid : IsFiniteSetoid (A.setoid ⇨ B.setoid) (B.N Nat.^ A.N)
--   _⟨$⟩_ (to (ontoFin function-isFiniteSetoid)) f = {!!}
--   cong (to (ontoFin function-isFiniteSetoid)) = {!!}
--   _⟨$⟩_ (from (ontoFin function-isFiniteSetoid)) i = {!!}
--   cong (from (ontoFin function-isFiniteSetoid)) = {!!}
--   left-inverse-of (ontoFin function-isFiniteSetoid) = {!!}

-- TODO: Prove dependent function spaces with finite domain and codomain are
-- finite sets, and recast as an instance of that.

module _ {a p ℓ} {A : Set a} (finiteAt : A → FiniteSet p ℓ) where
  private
    module PW x = FiniteSet (finiteAt x)
    module PW′ {x} = PW x
    open PW using () renaming (Carrier to P; N to boundAt)
    open PW′ using (_≈_)

    All≈ = All′.PW PW.setoid
    All-setoid = All′.PW-setoid PW.setoid
    open All′.PW PW.setoid

  finiteAllSize : List A → ℕ
  finiteAllSize = List.product ∘ List.map boundAt

  All-isFiniteSetoid : (xs : List A) → IsFiniteSetoid (All-setoid xs) _
  All-isFiniteSetoid _ = record
    { ontoFin = record
      { to = record { _⟨$⟩_ = to ; cong = to-cong }
      ; from = ≡.→-to-⟶ from
      ; left-inverse-of = left-inverse-of
      }
    }
    where
      prodIsSum : ∀ m n → m Nat.* n ≡ Table.foldr Nat._+_ 0 (Table.replicate {m} n)
      prodIsSum Nat.zero _ = ≡.refl
      prodIsSum (Nat.suc m) n = ≡.cong₂ Nat._+_ (≡.refl {x = n}) (prodIsSum m n)

      splitProd : ∀ {m n} → Fin (m Nat.* n) → Fin m × Fin n
      splitProd {m} {n} ij rewrite prodIsSum m n = Inverse.from (P.Pieces′.asPiece (P.constPieces m n)) ⟨$⟩ ij

      joinProd : ∀ {m n} → Fin m × Fin n → Fin (m Nat.* n)
      joinProd {m} {n} ij with Inverse.to (P.Pieces′.asPiece (P.constPieces m n )) ⟨$⟩ ij
      joinProd {m} {n} ij | f rewrite prodIsSum m n = f

      splitProd-joinProd : ∀ {m n} (ij : Fin m × Fin n) → splitProd (joinProd ij) ≡ ij
      splitProd-joinProd {m} {n} ij rewrite prodIsSum m n = Inverse.left-inverse-of (P.Pieces′.asPiece (P.constPieces m n)) ij

      to : ∀ {xs} → All P xs → Fin (finiteAllSize xs)
      to [] = Fin.zero
      to (_∷_ {x} {xs} px ap) = joinProd (PW.toIx _ px , to ap)

      to-cong : ∀ {xs}{apx apy : All P xs} → All≈ apx apy → to apx ≡ to apy
      to-cong [] = ≡.refl
      to-cong (p ∷ q) = ≡.cong₂ (λ i j → joinProd (i , j)) (cong (LeftInverse.to PW′.ontoFin) p) (to-cong q)

      from : ∀ {xs} → Fin (finiteAllSize xs) → All P xs
      from {List.[]} _ = []
      from {x List.∷ xs} i =
        (PW.fromIx _ (proj₁ (splitProd i))) ∷
        from {xs} (proj₂ (splitProd {boundAt x} i))

      left-inverse-of : ∀ {xs} (ap : All P xs) → All≈ (from (to ap)) ap
      left-inverse-of [] = Setoid.refl (All-setoid _)
      left-inverse-of (px ∷ ap) rewrite splitProd-joinProd (PW.toIx _ px , to ap) =
        PW′.fromIx-toIx px ∷ left-inverse-of ap

  All-finiteSet : List A → FiniteSet _ _
  All-finiteSet xs = record { isFiniteSetoid = All-isFiniteSetoid xs }


1-Truncate : ∀ {c ℓ} (setoid : Setoid c ℓ) → Setoid _ _
1-Truncate setoid = record
  { Carrier = Carrier
  ; _≈_ = λ _ _ → ⊤
  ; isEquivalence = record { refl = _ ; sym = _ ; trans = _ }
  }
  where open Setoid setoid

module DecFinite {a p} {A : Set a} {P : A → Set p} (decP : U.Decidable P) where
  P-setoid : A → Setoid _ _
  P-setoid = 1-Truncate ∘ ≡.setoid ∘ P

  P-size : A → ℕ
  P-size x = if ⌊ decP x ⌋ then 1 else 0

  P-isFinite : ∀ x → IsFiniteSetoid (P-setoid x) (P-size x)
  P-isFinite x with decP x
  P-isFinite x | yes p = record
    { ontoFin = record
      { to = record
        { _⟨$⟩_ = λ _ → Fin.zero ; cong = λ _ → ≡.refl }
        ; from = ≡.→-to-⟶ λ _ → p
        ; left-inverse-of = _
      }
    }
  P-isFinite x | no ¬p = record
    { ontoFin = record
      { to = record { _⟨$⟩_ = ⊥-elim ∘ ¬p ; cong = λ {x} → ⊥-elim (¬p x) }
      ; from = ≡.→-to-⟶ λ ()
      ; left-inverse-of = _
      }
    }

  Decidable-finite : A → FiniteSet p _
  Decidable-finite x = record { isFiniteSetoid = P-isFinite x }

module _ {c} {A : Set c} {N} (isFiniteSet : IsFiniteSet A N) {p} {P : A → Set p} (decP : U.Decidable P) where
  open IsFiniteSetoid isFiniteSet

  subsetFinite : FiniteSet _ _
  subsetFinite = Σ-finiteSet isFiniteSet (DecFinite.Decidable-finite decP)

  subset-isFiniteSet : ∀ {a′} {A′ : Set a′} → LeftInverse (≡.setoid A′) (FiniteSet.setoid subsetFinite) → IsFiniteSet A′ _
  subset-isFiniteSet = extendedIsFinite subsetFinite
