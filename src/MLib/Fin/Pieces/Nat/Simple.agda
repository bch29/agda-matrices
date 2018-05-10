module MLib.Fin.Pieces.Nat.Simple where

open import MLib.Prelude
open import MLib.Fin.Pieces.Core
open import MLib.Fin.Pieces.Nat

open Nat using (_*_; _+_; _<_)
open Fin using (toℕ; fromℕ≤)
open Table

repl : ∀ n → ℕ → Table ℕ n
repl _ = replicate

-- abstract
-- TODO: why does this break reduction later?
sum-replicate-* : ∀ m n → sum (repl m n) ≡ m * n
sum-replicate-* zero _ = ≡.refl
sum-replicate-* (suc m) _ = ≡.cong₂ _+_ ≡.refl (sum-replicate-* m _)

intoPiece : ∀ a b → ℕ × ℕ → ℕ
intoPiece a b = Piecesℕ.intoPiece (constPieces a b)

intoPiece³′ : ∀ a b c → ℕ × ℕ × ℕ → ℕ
intoPiece³′ a b c (i , j , k) = intoPiece a (b * c) (i , intoPiece b c (j , k))

intoPiece³ : ∀ a b c → ℕ × ℕ × ℕ → ℕ
intoPiece³ a b c (i , j , k) = intoPiece (a * b) c (intoPiece a b (i , j) , k)

open ≡.Reasoning

abstract
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

  intoPiece-assoc :
    ∀ {a b c} i j k → i < a → j < b → k < c →
    intoPiece³′ a b c (i , j , k) ≡ intoPiece³ a b c (i , j , k)
  intoPiece-assoc {a} {b} {c} zero zero k p q r = ≡.refl
  intoPiece-assoc {suc a} {suc b} {c} zero (suc j) k (Nat.s≤s p) (Nat.s≤s q) r =
    begin
      intoPiece³′ (suc a) (suc b) c (0 , suc j , k)   ≡⟨⟩
      intoPiece (suc b) c (suc j , k)                 ≡⟨⟩
      c + intoPiece b c (j , k)                       ≡⟨ ≡.cong₂ _+_ ≡.refl (intoPiece′-a-irrel b (a * suc b) c j k q r) ⟩
      c + intoPiece (b + a * suc b) c (j , k)         ≡⟨⟩
      intoPiece (suc (b + a * suc b)) c (suc j , k)   ≡⟨⟩
      intoPiece (suc a * suc b) c (suc j , k)         ≡⟨⟩
      intoPiece³ (suc a) (suc b) c (0 , suc j , k)    ∎
  intoPiece-assoc {zero} {b} {c} (suc i) j k () q r
  intoPiece-assoc {suc a} {b} {c} (suc i) zero k (Nat.s≤s p) q r =
    begin
      intoPiece³′ (suc a) b c (suc i , 0 , k)   ≡⟨⟩
      intoPiece (suc a) (b * c) (suc i , k)   ≡⟨ lem (suc a) b c (suc i) k (Nat.s≤s p) ⟩
      intoPiece (suc a * b) c (suc i * b , k) ≡⟨ ≡.cong (λ h → intoPiece (suc a * b) c (b + h , k)) (≡.sym (intoPiece′-0 a b i p)) ⟩
      intoPiece (suc a * b) c (b + intoPiece a b (i , 0) , k) ≡⟨⟩
      intoPiece (suc a * b) c (intoPiece (suc a) b (suc i , 0) , k) ≡⟨⟩
      intoPiece³ (suc a) b c (suc i , 0 , k)  ∎
  intoPiece-assoc {suc a} {zero} {c} (suc i) (suc j) k p () r
  intoPiece-assoc {suc a} {suc b} {c} (suc i) (suc j) k (Nat.s≤s p) q r =
    let sb = suc b
        sj = suc j
    in begin
      intoPiece³′ (suc a) sb c (suc i , sj , k)                          ≡⟨⟩
      intoPiece (suc a) (sb * c) (suc i , intoPiece sb c (sj , k))       ≡⟨⟩
      sb * c + intoPiece a (sb * c) (i , c + intoPiece b c (j , k))      ≡⟨⟩
      sb * c + intoPiece³′  a sb c (i , sj , k)                          ≡⟨ ≡.cong₂ _+_ ≡.refl (intoPiece-assoc i sj k p q r) ⟩
      sb * c + intoPiece³ a sb c (i , sj , k)                            ≡⟨⟩
      sb * c + intoPiece (a * sb) c (intoPiece a sb (i , sj) , k)        ≡⟨ Nat.+-assoc c _ _ ⟩
      c + (b * c + intoPiece (a * sb) c (intoPiece a sb (i , sj) , k))   ≡⟨ ≡.cong₂ _+_ ≡.refl (lem′ b (a * sb) c _ k) ⟩
      c + intoPiece (b + a * sb) c (b + intoPiece a sb (i , sj) , k)     ≡⟨⟩
      intoPiece (suc a * sb) c (intoPiece (suc a) sb (suc i , sj) , k)   ≡⟨⟩
      intoPiece³ (suc a) sb c (suc i , sj , k) ∎

abstract
  fromPiece-1ˡ : ∀ {b} i → i < b → Piecesℕ.fromPiece (constPieces 1 b) i ≡ (0 , i)
  fromPiece-1ˡ {b} i p with Impl.compare′ i b
  fromPiece-1ˡ {.(suc (i + k))} i p | Impl.less .i k = ≡.refl
  fromPiece-1ˡ {.m} .(m + k) p | Impl.gte m k = ⊥-elim (Nat.m+n≮m m k p)

  fromPiece-1ʳ : ∀ {a} i → i < a → Piecesℕ.fromPiece (constPieces a 1) i ≡ (i , 0)
  fromPiece-1ʳ {zero} _ ()
  fromPiece-1ʳ {suc a} zero p = ≡.refl
  fromPiece-1ʳ {suc a} (suc i) (Nat.s≤s p) with Σ.≡⇒≡×≡ (fromPiece-1ʳ {a} i p)
  fromPiece-1ʳ {suc a} (suc i) (Nat.s≤s p) | q , r with Impl.compare′ i 0
  fromPiece-1ʳ {suc a} (suc i) (Nat.s≤s p) | q , r | Impl.gte .0 .i = Σ.≡×≡⇒≡ (≡.cong suc q , r)
