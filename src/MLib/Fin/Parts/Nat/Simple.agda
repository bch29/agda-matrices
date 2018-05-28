module MLib.Fin.Parts.Nat.Simple where

open import MLib.Prelude
open import MLib.Fin.Parts.Core
open import MLib.Fin.Parts.Nat

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

intoPart : ∀ a b → ℕ × ℕ → ℕ
intoPart a b = Partsℕ.intoPart (constParts a b)

intoPart³′ : ∀ a b c → ℕ × ℕ × ℕ → ℕ
intoPart³′ a b c (i , j , k) = intoPart a (b * c) (i , intoPart b c (j , k))

intoPart³ : ∀ a b c → ℕ × ℕ × ℕ → ℕ
intoPart³ a b c (i , j , k) = intoPart (a * b) c (intoPart a b (i , j) , k)

open ≡.Reasoning

abstract
  intoPart′-a-irrel : ∀ a k b i j → i < a → j < b → intoPart a b (i , j) ≡ intoPart (a + k) b (i , j)
  intoPart′-a-irrel a k b zero j p q = ≡.refl
  intoPart′-a-irrel (suc a) k b (suc i) j (Nat.s≤s p) q = ≡.cong₂ _+_ ≡.refl (intoPart′-a-irrel a k b i j p q)

  intoPart′-0 : ∀ a b i → i < a → intoPart a b (i , 0) ≡ i * b
  intoPart′-0 zero b i ()
  intoPart′-0 (suc a) b zero (Nat.s≤s p) = ≡.refl
  intoPart′-0 (suc a) b (suc i) (Nat.s≤s p) = ≡.cong₂ _+_ ≡.refl (intoPart′-0 a b i p)

  lem′ : ∀ m a b i j → (m * b) + intoPart a b (i , j) ≡ intoPart (m + a) b (m + i , j)
  lem′ zero a b i j = ≡.refl
  lem′ (suc m) a b i j =
    begin
      b + m * b + intoPart a b (i , j)   ≡⟨ Nat.+-assoc b _ _ ⟩
      b + (m * b + intoPart a b (i , j)) ≡⟨ ≡.cong₂ _+_ ≡.refl (lem′ m a b i j) ⟩
      b + intoPart (m + a) b (m + i , j) ∎

  lem : ∀ a b c i k → i < a → intoPart a (b * c) (i , k) ≡ intoPart (a * b) c (i * b , k)
  lem zero b c i k ()
  lem (suc a) b c zero k p = ≡.refl
  lem (suc a) b c (suc i) k (Nat.s≤s p) =
    begin
      (b * c) + intoPart a (b * c) (i , k)      ≡⟨ ≡.cong₂ _+_ ≡.refl (lem a b c i k p) ⟩
      (b * c) + intoPart (a * b) c (i * b , k)  ≡⟨ lem′ b (a * b) c (i * b) k ⟩
      intoPart (suc a * b) c (suc i * b , k)    ∎

  intoPart-assoc :
    ∀ {a b c} i j k → i < a → j < b → k < c →
    intoPart³′ a b c (i , j , k) ≡ intoPart³ a b c (i , j , k)
  intoPart-assoc {a} {b} {c} zero zero k p q r = ≡.refl
  intoPart-assoc {suc a} {suc b} {c} zero (suc j) k (Nat.s≤s p) (Nat.s≤s q) r =
    begin
      intoPart³′ (suc a) (suc b) c (0 , suc j , k)   ≡⟨⟩
      intoPart (suc b) c (suc j , k)                 ≡⟨⟩
      c + intoPart b c (j , k)                       ≡⟨ ≡.cong₂ _+_ ≡.refl (intoPart′-a-irrel b (a * suc b) c j k q r) ⟩
      c + intoPart (b + a * suc b) c (j , k)         ≡⟨⟩
      intoPart (suc (b + a * suc b)) c (suc j , k)   ≡⟨⟩
      intoPart (suc a * suc b) c (suc j , k)         ≡⟨⟩
      intoPart³ (suc a) (suc b) c (0 , suc j , k)    ∎
  intoPart-assoc {zero} {b} {c} (suc i) j k () q r
  intoPart-assoc {suc a} {b} {c} (suc i) zero k (Nat.s≤s p) q r =
    begin
      intoPart³′ (suc a) b c (suc i , 0 , k)   ≡⟨⟩
      intoPart (suc a) (b * c) (suc i , k)   ≡⟨ lem (suc a) b c (suc i) k (Nat.s≤s p) ⟩
      intoPart (suc a * b) c (suc i * b , k) ≡⟨ ≡.cong (λ h → intoPart (suc a * b) c (b + h , k)) (≡.sym (intoPart′-0 a b i p)) ⟩
      intoPart (suc a * b) c (b + intoPart a b (i , 0) , k) ≡⟨⟩
      intoPart (suc a * b) c (intoPart (suc a) b (suc i , 0) , k) ≡⟨⟩
      intoPart³ (suc a) b c (suc i , 0 , k)  ∎
  intoPart-assoc {suc a} {zero} {c} (suc i) (suc j) k p () r
  intoPart-assoc {suc a} {suc b} {c} (suc i) (suc j) k (Nat.s≤s p) q r =
    let sb = suc b
        sj = suc j
    in begin
      intoPart³′ (suc a) sb c (suc i , sj , k)                          ≡⟨⟩
      intoPart (suc a) (sb * c) (suc i , intoPart sb c (sj , k))       ≡⟨⟩
      sb * c + intoPart a (sb * c) (i , c + intoPart b c (j , k))      ≡⟨⟩
      sb * c + intoPart³′  a sb c (i , sj , k)                          ≡⟨ ≡.cong₂ _+_ ≡.refl (intoPart-assoc i sj k p q r) ⟩
      sb * c + intoPart³ a sb c (i , sj , k)                            ≡⟨⟩
      sb * c + intoPart (a * sb) c (intoPart a sb (i , sj) , k)        ≡⟨ Nat.+-assoc c _ _ ⟩
      c + (b * c + intoPart (a * sb) c (intoPart a sb (i , sj) , k))   ≡⟨ ≡.cong₂ _+_ ≡.refl (lem′ b (a * sb) c _ k) ⟩
      c + intoPart (b + a * sb) c (b + intoPart a sb (i , sj) , k)     ≡⟨⟩
      intoPart (suc a * sb) c (intoPart (suc a) sb (suc i , sj) , k)   ≡⟨⟩
      intoPart³ (suc a) sb c (suc i , sj , k) ∎

abstract
  fromPart-1ˡ : ∀ {b} i → i < b → Partsℕ.fromPart (constParts 1 b) i ≡ (0 , i)
  fromPart-1ˡ {b} i p with Impl.compare′ i b
  fromPart-1ˡ {.(suc (i + k))} i p | Impl.less .i k = ≡.refl
  fromPart-1ˡ {.m} .(m + k) p | Impl.gte m k = ⊥-elim (Nat.m+n≮m m k p)

  fromPart-1ʳ : ∀ {a} i → i < a → Partsℕ.fromPart (constParts a 1) i ≡ (i , 0)
  fromPart-1ʳ {zero} _ ()
  fromPart-1ʳ {suc a} zero p = ≡.refl
  fromPart-1ʳ {suc a} (suc i) (Nat.s≤s p) with Σ.≡⇒≡×≡ (fromPart-1ʳ {a} i p)
  fromPart-1ʳ {suc a} (suc i) (Nat.s≤s p) | q , r with Impl.compare′ i 0
  fromPart-1ʳ {suc a} (suc i) (Nat.s≤s p) | q , r | Impl.gte .0 .i = Σ.≡×≡⇒≡ (≡.cong suc q , r)
