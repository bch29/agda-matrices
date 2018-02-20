module MLib.Prelude.Fin.Pieces where

open import MLib.Prelude.FromStdlib
open import MLib.Prelude.Fin

open import Data.Table as Table using (Table) hiding (module Table)

open import Function.Inverse using (Inverse; _↔_)
open import Function.LeftInverse using (LeftInverse; _↞_)
open import Function.Surjection using (_↠_)
open import Function.Equality using (_⟶_; _⟨$⟩_; cong)
open import Function.Related renaming (module EquationalReasoning to BijReasoning)

import Relation.Binary.Indexed as I
import Data.Product.Relation.SigmaPointwise as Σ
import Data.Product.Relation.SigmaPropositional as OverΣ
open OverΣ using (OverΣ)

open import Data.Product using (_,′_)

open Nat using (zero; suc; _*_)
open Table

private
  sum : ∀ {n} → Table ℕ n → ℕ
  sum = foldr Nat._+_ 0

record Pieces {a} (A : Set a) (size : A → ℕ) : Set a where
  field
    numPieces : ℕ
    pieces : Table A numPieces

  pieceAt = lookup pieces
  sizeAt = size ∘ pieceAt
  totalSize = sum (map size pieces)

module _ {a} {A : Set a} {size : A → ℕ} (P : Pieces A size) where
  open Pieces P

  private
    intoPiece′ : (numPieces : ℕ) (pieces : Table ℕ numPieces) (i : Fin numPieces) → Fin (lookup pieces i) → Fin (sum pieces)
    intoPiece′ _ pieces zero j = inject+ (sum (tail pieces)) j
    intoPiece′ _ pieces (suc i) j = raise (lookup pieces zero) (intoPiece′ _ _ i j)

    fromPiece : {numPieces : ℕ} {pieces : Table ℕ numPieces} → Fin (sum pieces) → Σ (Fin numPieces) (Fin ∘ lookup pieces)
    fromPiece {zero} ()
    fromPiece {suc n} {pieces} k with reduce+ (lookup pieces zero) k
    fromPiece {suc n} k | inj₁ (k′ , _) = zero , k′
    fromPiece {suc n} k | inj₂ (k′ , _) with fromPiece {n} k′
    fromPiece {suc n} {_} k | inj₂ (k′ , _) | i , j = suc i , j

    fromPiece-intoPiece : {numPieces : ℕ} {pieces : Table ℕ numPieces} (i : Fin numPieces) (j : Fin (lookup pieces i)) → fromPiece (intoPiece′ numPieces pieces i j) ≡ (i , j)
    fromPiece-intoPiece {numPieces} {pieces} zero j with reduce+ (lookup pieces zero) (inject+ (sum (tail pieces)) j)
    fromPiece-intoPiece {.(suc _)} {_} zero j | inj₁ (k , p) rewrite inject+-injective p = ≡.refl
    fromPiece-intoPiece {.(suc _)} {pieces} zero j | inj₂ (k , p) = ⊥-elim (raise≢ (sum (tail pieces)) (lookup pieces zero) p)
    fromPiece-intoPiece {_} {pieces} (suc i) j with reduce+ (lookup pieces zero) (raise (lookup pieces zero) (intoPiece′ _ (tail pieces) i j))
    fromPiece-intoPiece {.(suc _)} {pieces} (suc i) j | inj₁ (k , p) = ⊥-elim (raise≢ (sum (tail pieces)) (lookup pieces zero) (≡.sym p))
    fromPiece-intoPiece {.(suc _)} {pieces} (suc {numPieces} i) j | inj₂ (k , p) = lem′ i j k lem
      where
        open ≡.Reasoning

        lem : fromPiece {pieces = tail pieces} k ≡ (i , j)
        lem = begin
          fromPiece k                                  ≡⟨ ≡.cong fromPiece (raise-injective (lookup pieces zero) p) ⟩
          fromPiece (intoPiece′ _ (tail pieces) i j)   ≡⟨ fromPiece-intoPiece i j ⟩
          (i , j)                                      ∎

        lem′ : ∀ i (j : Fin (lookup (tail pieces) i)) k → fromPiece k ≡ (i , j) → (suc (proj₁ (fromPiece k)) , proj₂ (fromPiece {pieces = tail pieces} k)) ≡ (suc i , j)
        lem′ i j k p with OverΣ.from-≡ p
        lem′ .(proj₁ (fromPiece k)) j k p | ≡.refl , p2 = OverΣ.to-≡ (≡.refl , p2)

    intoPiece-fromPiece : (numPieces : ℕ) {pieces : Table ℕ numPieces} (k : Fin (sum pieces)) → uncurry (intoPiece′ numPieces pieces) (fromPiece k) ≡ k
    intoPiece-fromPiece zero ()
    intoPiece-fromPiece (suc numPieces) {pieces} k with reduce+ (lookup pieces zero) k
    intoPiece-fromPiece (suc numPieces) {_} k | inj₁ (k′ , p) = p
    intoPiece-fromPiece (suc numPieces) {pieces} k | inj₂ (k′ , p) =
      begin
        raise (lookup pieces zero) _  ≡⟨ ≡.cong (raise (lookup pieces zero)) (intoPiece-fromPiece _ {pieces = tail pieces} k′) ⟩
        raise (lookup pieces zero) k′ ≡⟨ p ⟩
        k ∎
      where
        open ≡.Reasoning


  intoPiece : (i : Fin numPieces) → Fin (sizeAt i) → Fin totalSize
  intoPiece = intoPiece′ _ _

  asPiece : Σ (Fin numPieces) (Fin ∘ sizeAt) ↔ Fin totalSize
  asPiece = record
    { to = ≡.→-to-⟶ (uncurry intoPiece)
    ; from = ≡.→-to-⟶ fromPiece
    ; inverse-of = record
      { left-inverse-of = λ _ → fromPiece-intoPiece _ _
      ; right-inverse-of = intoPiece-fromPiece numPieces
      }
    }

Pieces² : ∀ {a} (A : Set a) (size : A → ℕ) → Set a
Pieces² A size = Pieces (Pieces A size) (Pieces.totalSize)

private
  Σ-bij : ∀ {a b c} {A : Set a} {B : A → Set b} {C : A → Set c} → (∀ x → B x ↔ C x) → Σ A B ↔ Σ A C
  Σ-bij pw = record
    { to = ≡.→-to-⟶ (uncurry λ x y → x , Inverse.to (pw x) ⟨$⟩ y)
    ; from = ≡.→-to-⟶ (uncurry λ x y → x , Inverse.from (pw x) ⟨$⟩ y)
    ; inverse-of = record
      { left-inverse-of = uncurry λ x y → OverΣ.to-≡ (≡.refl , Inverse.left-inverse-of (pw x) y)
      ; right-inverse-of = uncurry λ x y → OverΣ.to-≡ (≡.refl , Inverse.right-inverse-of (pw x) y)
      }
    }

module _ {a} {A : Set a} {size : A → ℕ} (P₁ : Pieces² A size) where
  private
    module P₁ = Pieces P₁

  module _ (i : Fin P₁.numPieces) where
    private
      P₂ = P₁.pieceAt i
      module P₂ = Pieces P₂

    intoPiece² : (j : Fin P₂.numPieces) → Fin (size (P₂.pieceAt j)) → Fin P₁.totalSize
    intoPiece² j = intoPiece P₁ i ∘ intoPiece P₂ j

  asPiece² :
    Σ (Fin P₁.numPieces) (λ i →
      let P₂ = P₁.pieceAt i
          module P₂ = Pieces P₂
      in Σ (Fin P₂.numPieces) (Fin ∘ P₂.sizeAt))
    ↔ Fin P₁.totalSize
  asPiece² =
      Σ (Fin P₁.numPieces) (λ i →
        let P₂ = P₁.pieceAt i
            module P₂ = Pieces P₂
        in Σ (Fin P₂.numPieces) (Fin ∘ P₂.sizeAt))
    ↔⟨ Σ-bij (asPiece ∘ P₁.pieceAt) ⟩
      Σ (Fin P₁.numPieces) (Fin ∘ P₁.sizeAt)
    ↔⟨ asPiece P₁ ⟩
      Fin P₁.totalSize
    ∎
    where open BijReasoning

constPieces : ℕ → ℕ → Pieces ℕ id
constPieces numPieces pieceSize = record
  { numPieces = numPieces
  ; pieces = replicate pieceSize
  }

{-

Need an injection
A ↣ ∃ K

and for each x

s x : ℕ
K x ↣ Fin (s x)

-}

-- record PiecewiseLInv {a} {A : Set a}

record Constructor {a} {b} (A : Set a) (B : Set b) : Set (a ⊔ˡ b) where
  field
    build : A → B
    constructive : ∀ x y → build x ≡ y → ∃ λ z → x ≡ z × build z ≡ y


private
  Σ-↞ : ∀ {a b c} {A : Set a} {B : A → Set b} {C : A → Set c} → (∀ x → B x ↞ C x) → Σ A B ↞ Σ A C
  Σ-↞ f = record
    { to = ≡.→-to-⟶ (uncurry λ x y → x , LeftInverse.to (f x) ⟨$⟩ y)
    ; from = ≡.→-to-⟶ (uncurry λ x y → x , LeftInverse.from (f x) ⟨$⟩ y)
    ; left-inverse-of = uncurry λ x y → OverΣ.to-≡ (≡.refl , LeftInverse.left-inverse-of (f x) y)
    }

module _ {a b} {A : Set a} {B : Set b} {size : A → ℕ} (P : Pieces A size) where
  open Pieces P

  open import Function.Related


  liftConstructors : ∀ {c} (Arg : Fin numPieces → Set c) → (∀ i → Arg i ↞ Fin (sizeAt i)) → B ↞ ∃ Arg → B ↞ Fin totalSize
  liftConstructors Arg ontoArgAt constructAt =
      B                                ∼⟨ constructAt ⟩
      Σ (Fin numPieces) Arg            ∼⟨ Σ-↞ ontoArgAt ⟩
      Σ (Fin numPieces) (Fin ∘ sizeAt) ↔⟨ asPiece P ⟩
      Fin totalSize                    ∎
    where open EquationalReasoning


  piecewiseRel :
    ∀ {k}
    → (f : Σ (Fin numPieces) (Fin ∘ sizeAt) ∼[ k ] B)
    → Fin totalSize ∼[ k ] B
  piecewiseRel f =
      Fin totalSize   ↔⟨ sym (asPiece P) ⟩
      Σ (Fin numPieces) (Fin ∘ sizeAt) ∼⟨ f ⟩
      B ∎
    where open EquationalReasoning


module _ {c₁ ℓ₁ c₂ ℓ₂ c₃ ℓ₃}
         (A-setoid : Setoid c₁ ℓ₁)
         (I-setoid : Setoid c₂ ℓ₂)
         (K-setoid : I.Setoid (Setoid.Carrier I-setoid) c₃ ℓ₃)
         (A-to-K : LeftInverse A-setoid (Σ.setoid I-setoid K-setoid))
         (sizeAtI : I-setoid ⟶ ≡.setoid ℕ)
         (fromK : ∀ i → LeftInverse (K-setoid I.at i) (≡.setoid (Fin (sizeAtI ⟨$⟩ i))))
         where

--   open Setoid A-setoid using () renaming (Carrier to A)
--   open Setoid B-setoid using () renaming (Carrier to B)

--   module _ {size : A → ℕ} (P : Pieces A size) where
--     open Pieces P

--   module _ (intoA-size : LeftInverse B-setoid (≡.setoid (Fin numPieces))) where
--            (invAt : ∀ i → LeftInverse A-setoid (≡.setoid (Fin (Pieces.sizeAt P i)))) where

--     liftLeftInverses : LeftInverse B-setoid (≡.setoid (Fin totalSize))
--     liftLeftInverses = record
--       { to = record
--         { _⟨$⟩_ = appTo
--         ; cong = {!!}
--         }
--       ; from = ≡.→-to-⟶ {!!}
--       ; left-inverse-of = {!!}
--       }
--       where
--         appTo : B → Fin totalSize
--         appTo y = ?
--           -- let x = LeftInverse.to intoA ⟨$⟩ y
--           -- in {!!}
