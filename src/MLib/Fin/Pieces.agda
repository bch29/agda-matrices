module MLib.Fin.Pieces where

open import MLib.Prelude
open import MLib.Prelude.RelProps

open import Function.Surjection using (_↠_)
open import Function.Related renaming (module EquationalReasoning to BijReasoning)

import Relation.Binary.Indexed as I

open Nat using (_*_; _+_; _<_)
open Fin using (toℕ; fromℕ≤)
open Table

private
  sum : ∀ {n} → Table ℕ n → ℕ
  sum = foldr _+_ 0

record Pieces {a} (A : Set a) (size : A → ℕ) : Set a where
  field
    numPieces : ℕ
    pieces : Table A numPieces

  pieceAt = lookup pieces
  sizeAt = size ∘ pieceAt
  totalSize = sum (map size pieces)
  pieceSizes = tabulate sizeAt

tryLookup : ∀ {n} {a} {A : Set a} → A → Table A n → ℕ → A
tryLookup {n = zero} z t _ = z
tryLookup {n = suc n} z t zero = lookup t zero
tryLookup {n = suc n} z t (suc i) = tryLookup z (tail t) i

tryLookup-prop : ∀ {n} {a} {A : Set a} {z : A} (t : Table A n) {i : Fin n} → lookup t i ≡ tryLookup z t (Fin.toℕ i)
tryLookup-prop _ {i = zero} = ≡.refl
tryLookup-prop t {i = suc i} = tryLookup-prop (tail t)

data Ordering′ : ℕ → ℕ → Set where
  less : ∀ m k → Ordering′ m (suc (m + k))
  gte : ∀ m k → Ordering′ (m + k) m

compare′ : ∀ m n → Ordering′ m n
compare′ zero zero = gte zero zero
compare′ zero (suc n) = less zero n
compare′ (suc m) zero = gte zero (suc m)
compare′ (suc m) (suc n) with compare′ m n
compare′ (suc m) (suc .(suc (m + k))) | less .m k = less (suc m) k
compare′ (suc .(n + k)) (suc n) | gte .n k = gte (suc n) k

module OnNat where
  -- Core lemmas

  lz-lem : ∀ a b c → a + b < a + c → b < c
  lz-lem zero b c p = p
  lz-lem (suc a) b c p = lz-lem a b c (Nat.+-cancelˡ-≤ 1 p)

  lz-lem₂ : ∀ a b → a < a + b → 0 < b
  lz-lem₂ zero b p = p
  lz-lem₂ (suc a) b p = lz-lem₂ a b (Nat.+-cancelˡ-≤ 1 p)

  fromℕ≤-cong′ : ∀ {a b m n} {p : a < m} {q : b < n} → m ≡ n → a ≡ b → fromℕ≤ {a} p ≅ fromℕ≤ {b} q
  fromℕ≤-cong′ {p = Nat.s≤s Nat.z≤n} {Nat.s≤s Nat.z≤n} ≡.refl ≡.refl = ≅.refl
  fromℕ≤-cong′ {p = Nat.s≤s (Nat.s≤s p)} {Nat.s≤s (Nat.s≤s q)} ≡.refl ≡.refl = ≅.cong suc (fromℕ≤-cong′ {p = Nat.s≤s p} {q = Nat.s≤s q} ≡.refl ≡.refl)

  fromℕ≤-cong : ∀ {a b n} {p : a < n} {q : b < n} → a ≡ b → fromℕ≤ {a} p ≡ fromℕ≤ {b} q
  fromℕ≤-cong = ≅.≅-to-≡ ∘ fromℕ≤-cong′ ≡.refl

  -- Core functions

  intoPiece : {numPieces : ℕ} (pieces : Table ℕ numPieces) → ℕ × ℕ → ℕ
  intoPiece pieces (zero , j) = j
  intoPiece {zero} pieces (suc i , j) = 0
  intoPiece {suc numPieces} pieces (suc i , j) = lookup pieces zero + intoPiece (tail pieces) (i , j)

  fromPiece : {numPieces : ℕ} (pieces : Table ℕ numPieces) (k : ℕ) → ℕ × ℕ
  fromPiece {zero} pieces k = 0 , 0
  fromPiece {suc n} pieces k with lookup pieces zero | compare′ k (lookup pieces zero)
  fromPiece {suc n} pieces k | .(suc (k + k₁)) | less .k k₁ = 0 , k
  fromPiece {suc n} pieces .(lz + k) | lz | gte .lz k =
    let i , j = fromPiece (tail pieces) k
    in (suc i , j)

  -- Property lemmas

  +-<-lem : ∀ {a b c} → b < c → a + b < a + c
  +-<-lem {zero} p = p
  +-<-lem {suc a} p = Nat.s≤s (+-<-lem p)

  fromℕ-suc-lem : ∀ {m n} (p : m < n) → suc (fromℕ≤ p) ≡ fromℕ≤ (Nat.s≤s p)
  fromℕ-suc-lem (Nat.s≤s p) = ≡.refl

  -- Properties

  intoPiece-prop : ∀ {numPieces} (pieces : Table ℕ numPieces) {i j} → i < numPieces → j < tryLookup 0 pieces i → intoPiece pieces (i , j) < sum pieces
  intoPiece-prop {suc numPieces} _ {zero} (Nat.s≤s p) q = Nat.≤-trans q (Nat.m≤m+n _ _)
  intoPiece-prop {suc numPieces} pieces {suc i} (Nat.s≤s p) q = +-<-lem (intoPiece-prop (tail pieces) p q)

  fromPiece-prop : ∀ {numPieces : ℕ} (pieces : Table ℕ numPieces) {k} → k < sum pieces →
    let i , j = fromPiece pieces k
    in Σ (i < numPieces) (λ q → j < lookup pieces (fromℕ≤ {i} q))
  fromPiece-prop {zero} pieces {k} ()
  fromPiece-prop {suc numPieces} pieces {k} p with lookup pieces zero | compare′ k (lookup pieces zero) | ≡.inspect (lookup pieces) zero
  fromPiece-prop {suc numPieces} pieces {k} p | .(suc (k + k₁)) | less .k k₁ | ≡.[ eq ] =
    Nat.s≤s Nat.z≤n ,
    Nat.≤-trans (Nat.s≤s (Nat.m≤m+n _ _)) (Nat.≤-reflexive (≡.sym eq))
  fromPiece-prop {suc numPieces} pieces {.(lz + k)} p | lz | gte .lz k | insp =
    let q , r = fromPiece-prop (tail pieces) {k} (lz-lem _ _ _ p)
    in Nat.s≤s q , Nat.≤-trans r (Nat.≤-reflexive (≡.cong (lookup pieces) (fromℕ-suc-lem _)))

  fromPiece-intoPiece :
    {numPieces : ℕ} (pieces : Table ℕ numPieces) (i j : ℕ) (p : j < tryLookup 0 pieces i) →
    fromPiece pieces (intoPiece pieces (i , j)) ≡ (i , j)
  fromPiece-intoPiece {zero} _ i j ()
  fromPiece-intoPiece {suc numPieces} pieces i j p
    with lookup pieces zero
       | intoPiece pieces (i , j)
       | compare′ (intoPiece pieces (i , j)) (lookup pieces zero)
       | ≡.inspect (lookup pieces) zero
       | ≡.inspect (intoPiece pieces) (i , j)
  fromPiece-intoPiece {suc numPieces} pieces zero .ipi p
    | .(suc (ipi + k)) | ipi | less .ipi k | insp₁ | ≡.[ ≡.refl ]
    = ≡.refl
  fromPiece-intoPiece {suc numPieces} pieces zero .(lookup pieces zero + k) p
    | .(lookup pieces zero) | .(lookup pieces zero + k) | gte .(lookup pieces zero) k | ≡.[ ≡.refl ] | ≡.[ ≡.refl ]
    = ⊥-elim (Nat.n≮n _ (Nat.≤-trans p (Nat.m≤m+n _ k)))
  fromPiece-intoPiece {suc numPieces} pieces (suc i) j p
    | .(suc (ipi + k)) | ipi | less .ipi k | ≡.[ eq ] | ≡.[ eq₁ ]
    = let y = lookup pieces zero
          z = intoPiece _ (i , j)
      in ⊥-elim (Nat.m≢1+m+n y {z + k} (
         begin
           y                   ≡⟨ eq ⟩
           suc (ipi + k)       ≡⟨ ≡.cong (λ h → suc (h + k)) (≡.sym eq₁) ⟩
           suc ((y + z) + k)   ≡⟨ ≡.cong suc (Nat.+-assoc y z k) ⟩
           suc (y + (z + k))   ∎))
    where open ≡.Reasoning
  fromPiece-intoPiece {suc numPieces} pieces (suc i) j p
    | .(lookup pieces zero) | .(lookup pieces zero + k) | gte .(lookup pieces zero) k | ≡.[ ≡.refl ] | ≡.[ eq₁ ]
    with Nat.+-cancelˡ-≡ (lookup pieces zero) eq₁
  fromPiece-intoPiece {suc numPieces} pieces (suc i) j p
    | .(lookup pieces zero) | .(lookup pieces zero + k) | gte .(lookup pieces zero) k | ≡.[ ≡.refl ] | ≡.[ eq₁ ]
    | eq₂ rewrite ≡.sym eq₂
    = let q , r = Σ.≡⇒Pointwise-≡ (fromPiece-intoPiece (tail pieces) i j p)
      in Σ.Pointwise-≡⇒≡ (≡.cong suc q , r)

  intoPiece-fromPiece : {numPieces : ℕ} (pieces : Table ℕ numPieces) (k : ℕ) (p : k < sum pieces) → intoPiece pieces (fromPiece pieces k) ≡ k
  intoPiece-fromPiece {zero} pieces k ()
  intoPiece-fromPiece {suc numPieces} pieces k p
    with lookup pieces zero
       | compare′ k (lookup pieces zero)
       | ≡.inspect (lookup pieces) zero
  intoPiece-fromPiece {suc numPieces} pieces k p | .(suc (k + k₁)) | less .k k₁ | insp = ≡.refl
  intoPiece-fromPiece {suc numPieces} pieces .(lookup pieces zero + k) p | .(lookup pieces zero) | gte .(lookup pieces zero) k | ≡.[ ≡.refl ]
    = ≡.cong₂ Nat._+_
      ≡.refl
      (intoPiece-fromPiece (tail pieces) k
        (Nat.+-cancelˡ-≤ (lookup pieces zero) (Nat.≤-trans (Nat.≤-reflexive (Nat.+-suc _ k)) p)))


module Pieces′ {a} {A : Set a} {size : A → ℕ} (P : Pieces A size) where
  open Pieces P public

  intoPieceℕ : ℕ × ℕ → ℕ
  intoPieceℕ = OnNat.intoPiece pieceSizes

  fromPieceℕ : ℕ → ℕ × ℕ
  fromPieceℕ = OnNat.fromPiece pieceSizes

  -- Fin functions

  intoPiece : Σ (Fin numPieces) (Fin ∘ sizeAt) → Fin totalSize
  intoPiece (i , j) =
    fromℕ≤ {intoPieceℕ (toℕ i , toℕ j)} (
      OnNat.intoPiece-prop pieceSizes
      (Fin.bounded i)
      (Nat.≤-trans (Fin.bounded j)
                   (Nat.≤-reflexive (tryLookup-prop pieceSizes))))

  fromPiece : Fin totalSize → Σ (Fin numPieces) (Fin ∘ sizeAt)
  fromPiece k =
    let p , q = OnNat.fromPiece-prop pieceSizes (Fin.bounded k)
    in fromℕ≤ p , fromℕ≤ q

  intoPiece-intoPieceℕ : (i : Fin numPieces) (j : Fin (sizeAt i)) → toℕ (intoPiece (i , j)) ≡ intoPieceℕ (toℕ i , toℕ j)
  intoPiece-intoPieceℕ _ _ = Fin.toℕ-fromℕ≤ _

  fromPiece-fromPieceℕ : (k : Fin totalSize) → Σ.map toℕ toℕ (fromPiece k) ≡ fromPieceℕ (toℕ k)
  fromPiece-fromPieceℕ k = Σ.≡×≡⇒≡ (Fin.toℕ-fromℕ≤ _ , Fin.toℕ-fromℕ≤ _)

  fromPiece-intoPiece : ∀ {i j} → fromPiece (intoPiece (i , j)) ≡ (i , j)
  fromPiece-intoPiece {i} {j} = Fin.toℕ-injective₂ (begin
    Σ.map toℕ toℕ (fromPiece (intoPiece (i , j)))   ≡⟨ fromPiece-fromPieceℕ _ ⟩
    fromPieceℕ (toℕ (intoPiece (i , j)))            ≡⟨ ≡.cong fromPieceℕ (intoPiece-intoPieceℕ i j) ⟩
    fromPieceℕ (intoPieceℕ (toℕ i , toℕ j))        ≡⟨ OnNat.fromPiece-intoPiece pieceSizes (toℕ i) (toℕ j) (Nat.≤-trans (Fin.bounded j) (Nat.≤-reflexive (tryLookup-prop pieceSizes))) ⟩
    (toℕ i , toℕ j)                                 ∎)
    where open ≡.Reasoning

  intoPiece-fromPiece : ∀ {k} → intoPiece (fromPiece k) ≡ k
  intoPiece-fromPiece {k} = Fin.toℕ-injective (
    begin
      toℕ (intoPiece (fromPiece k))               ≡⟨ uncurry intoPiece-intoPieceℕ (fromPiece k) ⟩
      intoPieceℕ (Σ.map toℕ toℕ (fromPiece k))   ≡⟨ ≡.cong intoPieceℕ (fromPiece-fromPieceℕ k) ⟩
      intoPieceℕ (fromPieceℕ (toℕ k))            ≡⟨ OnNat.intoPiece-fromPiece pieceSizes (toℕ k) (Fin.bounded k) ⟩
      toℕ k                                       ∎)
    where open ≡.Reasoning

  asPiece : Σ (Fin numPieces) (Fin ∘ sizeAt) ↔ Fin totalSize
  asPiece = record
    { to = ≡.→-to-⟶ intoPiece
    ; from = ≡.→-to-⟶ fromPiece
    ; inverse-of = record
      { left-inverse-of = λ _ → fromPiece-intoPiece
      ; right-inverse-of = λ _ → intoPiece-fromPiece
      }
    }

Pieces² : ∀ {a} (A : Set a) (size : A → ℕ) → Set a
Pieces² A size = Pieces (Pieces A size) Pieces.totalSize

module _ {a} {A : Set a} {size : A → ℕ} (P₁ : Pieces² A size) where
  private
    module P₁ = Pieces′ P₁

  module _ (i : Fin P₁.numPieces) where
    private
      P₂ = P₁.pieceAt i
      module P₂ = Pieces′ P₂

    intoPiece² : (j : Fin P₂.numPieces) → Fin (size (P₂.pieceAt j)) → Fin P₁.totalSize
    intoPiece² j = curry P₁.intoPiece i ∘ curry P₂.intoPiece j

  asPiece² :
    Σ (Fin P₁.numPieces) (λ i →
      let P₂ = P₁.pieceAt i
          module P₂ = Pieces P₂
      in Σ (Fin P₂.numPieces) (Fin ∘ P₂.sizeAt))
    ↔ Fin P₁.totalSize
  asPiece² =
      Σ (Fin P₁.numPieces) (λ i →
        let P₂ = P₁.pieceAt i
            module P₂ = Pieces′ P₂
        in Σ (Fin P₂.numPieces) (Fin ∘ P₂.sizeAt))
    ↔⟨ Σ-bij (Pieces′.asPiece ∘ P₁.pieceAt) ⟩
      Σ (Fin P₁.numPieces) (Fin ∘ P₁.sizeAt)
    ↔⟨ P₁.asPiece ⟩
      Fin P₁.totalSize
    ∎
    where open BijReasoning

constPieces : ℕ → ℕ → Pieces ℕ id
constPieces numPieces pieceSize = record
  { numPieces = numPieces
  ; pieces = replicate pieceSize
  }
