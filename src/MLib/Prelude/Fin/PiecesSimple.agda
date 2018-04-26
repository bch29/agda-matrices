module MLib.Prelude.Fin.PiecesSimple where

open import MLib.Prelude.FromStdlib
open import MLib.Prelude.Fin as Fin using (Fin; zero; suc) hiding (module Fin)
open import MLib.Prelude.Fin.Pieces

open import Function.Inverse using (_↔_; Inverse)
open import Function.Equality using (_⟨$⟩_)
-- import Relation.Binary.Indexed as I
-- open import Data.Product.Relation.Pointwise.Dependent as ΣR using (_,_)
-- open import Data.Product.Relation.Pointwise.NonDependent as ΣR′
open import Relation.Binary.HeterogeneousEquality as ≅ using (_≅_)

open Nat using (zero; suc; _*_; _+_; _<_)
open Fin using (toℕ; fromℕ≤)
open Table

private
  sum : ∀ {n} → Table ℕ n → ℕ
  sum = foldr Nat._+_ 0

  repl : ∀ n → ℕ → Table ℕ n
  repl _ = replicate

sum-replicate-* : ∀ m n → sum (repl m n) ≡ m * n
sum-replicate-* zero _ = ≡.refl
sum-replicate-* (suc m) _ = ≡.cong₂ _+_ ≡.refl (sum-replicate-* m _)

private
  module OnNat₃ where
    intoPiece : ∀ a b → ℕ × ℕ → ℕ
    intoPiece a b = OnNat.intoPiece (repl a b)

    intoPiece³′ : ∀ a b c → ℕ × ℕ × ℕ → ℕ
    intoPiece³′ a b c (i , j , k) = intoPiece a (b * c) (i , intoPiece b c (j , k))

    intoPiece³ : ∀ a b c → ℕ × ℕ × ℕ → ℕ
    intoPiece³ a b c (i , j , k) = intoPiece (a * b) c (intoPiece a b (i , j) , k)

    open ≡.Reasoning

    intoPiece′-a-irrel : ∀ a k b i j → i < a → j < b → intoPiece a b (i , j) ≡ intoPiece (a + k) b (i , j)
    intoPiece′-a-irrel a k b zero j p q = ≡.refl
    intoPiece′-a-irrel (suc a) k b (suc i) j (Nat.s≤s p) q = ≡.cong₂ _+_ ≡.refl (intoPiece′-a-irrel a k b i j p q)

    intoPiece′-0 : ∀ a b i → i < a → intoPiece a b (i , 0) ≡ i * b
    intoPiece′-0 zero b i ()
    intoPiece′-0 (suc a) b zero (Nat.s≤s p) = ≡.refl
    intoPiece′-0 (suc a) b (suc i) (Nat.s≤s p) = ≡.cong₂ _+_ ≡.refl (intoPiece′-0 a b i p)

    lem′ : ∀ m a b i j → (m * b) + intoPiece a b (i , j) ≡ intoPiece (m + a) b (m + i , j)
    lem′ zero a b i j = ≡.refl
    lem′ (suc m) a b i j =
      begin
        b + m * b + intoPiece a b (i , j)   ≡⟨ Nat.+-assoc b _ _ ⟩
        b + (m * b + intoPiece a b (i , j)) ≡⟨ ≡.cong₂ _+_ ≡.refl (lem′ m a b i j) ⟩
        b + intoPiece (m + a) b (m + i , j) ∎

    lem : ∀ a b c i k → i < a → intoPiece a (b * c) (i , k) ≡ intoPiece (a * b) c (i * b , k)
    lem zero b c i k ()
    lem (suc a) b c zero k p = ≡.refl
    lem (suc a) b c (suc i) k (Nat.s≤s p) =
      begin
        (b * c) + intoPiece a (b * c) (i , k)      ≡⟨ ≡.cong₂ _+_ ≡.refl (lem a b c i k p) ⟩
        (b * c) + intoPiece (a * b) c (i * b , k)  ≡⟨ lem′ b (a * b) c (i * b) k ⟩
        intoPiece (suc a * b) c (suc i * b , k)    ∎

    intoPiece-assocℕ :
      ∀ {a b c} i j k → i < a → j < b → k < c →
      intoPiece³′ a b c (i , j , k) ≡ intoPiece³ a b c (i , j , k)
    intoPiece-assocℕ {a} {b} {c} zero zero k p q r = ≡.refl
    intoPiece-assocℕ {suc a} {suc b} {c} zero (suc j) k (Nat.s≤s p) (Nat.s≤s q) r =
      begin
        intoPiece³′ (suc a) (suc b) c (0 , suc j , k)     ≡⟨⟩
        intoPiece (suc b) c (suc j , k)                 ≡⟨⟩
        c + intoPiece b c (j , k)                       ≡⟨ ≡.cong₂ _+_ ≡.refl (intoPiece′-a-irrel b (a * suc b) c j k q r) ⟩
        c + intoPiece (b + a * suc b) c (j , k)         ≡⟨⟩
        intoPiece (suc (b + a * suc b)) c (suc j , k)   ≡⟨⟩
        intoPiece (suc a * suc b) c (suc j , k)         ≡⟨⟩
        intoPiece³ (suc a) (suc b) c (0 , suc j , k)    ∎
    intoPiece-assocℕ {zero} {b} {c} (suc i) j k () q r
    intoPiece-assocℕ {suc a} {b} {c} (suc i) zero k (Nat.s≤s p) q r =
      begin
        intoPiece³′ (suc a) b c (suc i , 0 , k)   ≡⟨⟩
        intoPiece (suc a) (b * c) (suc i , k)   ≡⟨ lem (suc a) b c (suc i) k (Nat.s≤s p) ⟩
        intoPiece (suc a * b) c (suc i * b , k) ≡⟨ ≡.cong (λ h → intoPiece (suc a * b) c (b + h , k)) (≡.sym (intoPiece′-0 a b i p)) ⟩
        intoPiece (suc a * b) c (b + intoPiece a b (i , 0) , k) ≡⟨⟩
        intoPiece (suc a * b) c (intoPiece (suc a) b (suc i , 0) , k) ≡⟨⟩
        intoPiece³ (suc a) b c (suc i , 0 , k)  ∎
    intoPiece-assocℕ {suc a} {zero} {c} (suc i) (suc j) k p () r
    intoPiece-assocℕ {suc a} {suc b} {c} (suc i) (suc j) k (Nat.s≤s p) q r =
      let sb = suc b
          sj = suc j
      in begin
        intoPiece³′ (suc a) sb c (suc i , sj , k)                             ≡⟨⟩
        intoPiece (suc a) (sb * c) (suc i , intoPiece sb c (sj , k))       ≡⟨⟩
        sb * c + intoPiece a (sb * c) (i , c + intoPiece b c (j , k))      ≡⟨⟩
        sb * c + intoPiece³′  a sb c (i , sj , k)                             ≡⟨ ≡.cong₂ _+_ ≡.refl (intoPiece-assocℕ i sj k p q r) ⟩
        sb * c + intoPiece³ a sb c (i , sj , k)                             ≡⟨⟩
        sb * c + intoPiece (a * sb) c (intoPiece a sb (i , sj) , k)        ≡⟨ Nat.+-assoc c _ _ ⟩
        c + (b * c + intoPiece (a * sb) c (intoPiece a sb (i , sj) , k))   ≡⟨ ≡.cong₂ _+_ ≡.refl (lem′ b (a * sb) c _ k) ⟩
        c + intoPiece (b + a * sb) c (b + intoPiece a sb (i , sj) , k)     ≡⟨⟩
        intoPiece (suc a * sb) c (intoPiece (suc a) sb (suc i , sj) , k)   ≡⟨⟩
        intoPiece³ (suc a) sb c (suc i , sj , k) ∎

asPiece : ∀ {a b} → (Fin a × Fin b) ↔ Fin (a * b)
asPiece {a} {b} = ≡.subst (λ n → (Fin a × Fin b) ↔ Fin n) (sum-replicate-* a b) (Pieces′.asPiece (constPieces a b))

intoPiece : ∀ {a b} → Fin a × Fin b → Fin (a * b)
intoPiece = Inverse.to asPiece ⟨$⟩_

fromPiece : ∀ {a b} → Fin (a * b) → Fin a × Fin b
fromPiece = Inverse.from asPiece ⟨$⟩_

intoPiece³′ : ∀ {a b c} → Fin a × Fin b × Fin c → Fin (a * (b * c))
intoPiece³′ {a} {b} {c} (i , j , k) = intoPiece (i , intoPiece (j , k))

intoPiece³ : ∀ {a b c} → Fin a × Fin b × Fin c → Fin (a * b * c)
intoPiece³ {a} {b} {c} (i , j , k) = intoPiece (intoPiece (i , j) , k)

private
  intoPiece′ : ∀ {a b} → Fin a × Fin b → Fin (sum (repl a b))
  intoPiece′ {a} {b} ij = Pieces′.intoPiece (constPieces a b) ij

  asPiece′-prop : ∀ {a b} → asPiece {a} {b} ≅ Pieces′.asPiece (constPieces a b)
  asPiece′-prop {a} {b} = ≅.≡-subst-removable _ _ _

  intoPiece′-prop : ∀ {a b} (i : Fin a) (j : Fin b) → toℕ (intoPiece (i , j)) ≡ toℕ (intoPiece′ (i , j))
  intoPiece′-prop {a} {b} i j =
    ≅.≅-to-≡ (≅.icong (λ n → (Fin a × Fin b) ↔ Fin n)
                       (≡.sym (sum-replicate-* a b))
                       (λ {n} (ap : (Fin a × Fin b) ↔ Fin n) → toℕ (Inverse.to ap ⟨$⟩ (i , j)))
                       asPiece′-prop)

  Nat-intoPiece-prop : ∀ {a b} (i : Fin a) (j : Fin b) → toℕ (Pieces′.intoPiece (constPieces a b) (i , j)) ≡ OnNat₃.intoPiece a b (toℕ i , toℕ j)
  Nat-intoPiece-prop {a} {b} i j = begin
    toℕ (intoPiece′ (i , j))               ≡⟨ ≡.sym (intoPiece′-prop i j) ⟩
    toℕ (intoPiece (i , j))                ≡⟨ intoPiece′-prop i j ⟩
    toℕ (intoPiece′ (i , j))               ≡⟨ Pieces′.intoPiece-intoPieceℕ (constPieces a b) i j ⟩
    OnNat₃.intoPiece a b (toℕ i , toℕ j)  ∎
    where open ≡.Reasoning

  intoPiece₃-prop : ∀ {a b c} (i : Fin a) (j : Fin b) (k : Fin c) → toℕ (intoPiece³′ (i , j , k)) ≡ OnNat₃.intoPiece³′ a b c (toℕ i , toℕ j , toℕ k)
  intoPiece₃-prop {a} {b} {c} i j k =
    begin
      toℕ (intoPiece (i , intoPiece (j , k)))                                                 ≡⟨ intoPiece′-prop i _ ⟩
      toℕ (intoPiece′ (i , intoPiece (j , k)))                                                ≡⟨ Pieces′.intoPiece-intoPieceℕ (constPieces a (b * c)) i _ ⟩
      Pieces′.intoPieceℕ (constPieces a (b * c)) (toℕ i , toℕ (intoPiece (j , k)))           ≡⟨ ≡.cong₂ (λ x y → Pieces′.intoPieceℕ (constPieces a x) (toℕ i , y))
                                                                                                  (≡.sym (sum-replicate-* b c))
                                                                                                  (intoPiece′-prop j k) ⟩
      Pieces′.intoPieceℕ (constPieces a (sum (repl b c))) (toℕ i , toℕ (intoPiece′ (j , k)))  ≡⟨ ≡.sym (Pieces′.intoPiece-intoPieceℕ (constPieces a _) i _) ⟩
      toℕ (Pieces′.intoPiece (constPieces a (sum (repl b c))) (i , intoPiece′ (j , k)))        ≡⟨ Pieces′.intoPiece-intoPieceℕ (constPieces a (sum (repl b c))) i _ ⟩
      OnNat₃.intoPiece a (sum (repl b c)) (toℕ i , toℕ (intoPiece′ (j , k)))                  ≡⟨ ≡.cong₂ (λ x y → OnNat₃.intoPiece a x (toℕ i , y))
                                                                                                  (sum-replicate-* b c)
                                                                                                  (Nat-intoPiece-prop j k) ⟩
      OnNat₃.intoPiece a (b * c) (toℕ i , OnNat₃.intoPiece b c (toℕ j , toℕ k))               ∎
    where
    open ≡.Reasoning

  intoPiece₃′-prop : ∀ {a b c} (i : Fin a) (j : Fin b) (k : Fin c) → toℕ (intoPiece³ (i , j , k)) ≡ OnNat₃.intoPiece³ a b c (toℕ i , toℕ j , toℕ k)
  intoPiece₃′-prop {a} {b} {c} i j k =
    begin
      toℕ (intoPiece (intoPiece (i , j) , k))                                                  ≡⟨ intoPiece′-prop (intoPiece (i , j)) k ⟩
      toℕ (intoPiece′ (intoPiece (i , j) , k))                                                 ≡⟨ Pieces′.intoPiece-intoPieceℕ (constPieces (a * b) c) (intoPiece (i , j)) k ⟩
      Pieces′.intoPieceℕ (constPieces (a * b) c) (toℕ (intoPiece (i , j)) , toℕ k)            ≡⟨ ≡.cong₂ (λ x y → Pieces′.intoPieceℕ (constPieces x c) (y , toℕ k))
                                                                                                   (≡.sym (sum-replicate-* a b))
                                                                                                   (intoPiece′-prop i j) ⟩
      Pieces′.intoPieceℕ (constPieces (sum (repl a b)) c) (toℕ (intoPiece′ (i , j)) , toℕ k)   ≡⟨ ≡.sym (Pieces′.intoPiece-intoPieceℕ (constPieces _ c) (intoPiece′ (i , j)) k) ⟩
      toℕ (intoPiece′ (intoPiece′ (i , j) , k))                                                 ≡⟨ Pieces′.intoPiece-intoPieceℕ (constPieces _ c) (intoPiece′ (i , j)) k ⟩
      OnNat₃.intoPiece (sum (repl a b)) c (toℕ (intoPiece′ (i , j)) , toℕ k)                   ≡⟨ ≡.cong₂ (λ x y → OnNat₃.intoPiece x c (y , toℕ k))
                                                                                                   (sum-replicate-* a b)
                                                                                                   (Nat-intoPiece-prop i j) ⟩
      OnNat₃.intoPiece (a * b) c (OnNat₃.intoPiece a b (toℕ i , toℕ j) , toℕ k)                ∎
    where open ≡.Reasoning

intoPiece-assoc : ∀ {a b c} (i : Fin a) (j : Fin b) (k : Fin c) → intoPiece³′ (i , j , k) ≅ intoPiece³ (i , j , k)
intoPiece-assoc {a} {b} {c} i j k =
  Fin.toℕ-injective′ (begin
    toℕ (intoPiece³′ (i , j , k)) ≡⟨ intoPiece₃-prop i j k ⟩
    OnNat₃.intoPiece³′ a b c (toℕ i , toℕ j , toℕ k) ≡⟨ OnNat₃.intoPiece-assocℕ _ _ _ (Fin.bounded i) (Fin.bounded j) (Fin.bounded k) ⟩
    OnNat₃.intoPiece³ a b c (toℕ i , toℕ j , toℕ k) ≡⟨ ≡.sym (intoPiece₃′-prop i j k) ⟩
    toℕ (intoPiece³ (i , j , k)) ∎)
  (≡.sym (Nat.*-assoc a _ _))
  where open ≡.Reasoning
