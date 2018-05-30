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

fromParts : ∀ a b → ℕ × ℕ → ℕ
fromParts a b = Partsℕ.fromParts (constParts a b)

fromParts³′ : ∀ a b c → ℕ × ℕ × ℕ → ℕ
fromParts³′ a b c (i , j , k) = fromParts a (b * c) (i , fromParts b c (j , k))

fromParts³ : ∀ a b c → ℕ × ℕ × ℕ → ℕ
fromParts³ a b c (i , j , k) = fromParts (a * b) c (fromParts a b (i , j) , k)

open ≡.Reasoning

abstract
  fromParts′-a-irrel : ∀ a k b i j → i < a → j < b → fromParts a b (i , j) ≡ fromParts (a + k) b (i , j)
  fromParts′-a-irrel a k b zero j p q = ≡.refl
  fromParts′-a-irrel (suc a) k b (suc i) j (Nat.s≤s p) q = ≡.cong₂ _+_ ≡.refl (fromParts′-a-irrel a k b i j p q)

  fromParts′-0 : ∀ a b i → i < a → fromParts a b (i , 0) ≡ i * b
  fromParts′-0 zero b i ()
  fromParts′-0 (suc a) b zero (Nat.s≤s p) = ≡.refl
  fromParts′-0 (suc a) b (suc i) (Nat.s≤s p) = ≡.cong₂ _+_ ≡.refl (fromParts′-0 a b i p)

  lem′ : ∀ m a b i j → (m * b) + fromParts a b (i , j) ≡ fromParts (m + a) b (m + i , j)
  lem′ zero a b i j = ≡.refl
  lem′ (suc m) a b i j =
    begin
      b + m * b + fromParts a b (i , j)   ≡⟨ Nat.+-assoc b _ _ ⟩
      b + (m * b + fromParts a b (i , j)) ≡⟨ ≡.cong₂ _+_ ≡.refl (lem′ m a b i j) ⟩
      b + fromParts (m + a) b (m + i , j) ∎

  lem : ∀ a b c i k → i < a → fromParts a (b * c) (i , k) ≡ fromParts (a * b) c (i * b , k)
  lem zero b c i k ()
  lem (suc a) b c zero k p = ≡.refl
  lem (suc a) b c (suc i) k (Nat.s≤s p) =
    begin
      (b * c) + fromParts a (b * c) (i , k)      ≡⟨ ≡.cong₂ _+_ ≡.refl (lem a b c i k p) ⟩
      (b * c) + fromParts (a * b) c (i * b , k)  ≡⟨ lem′ b (a * b) c (i * b) k ⟩
      fromParts (suc a * b) c (suc i * b , k)    ∎

  fromParts-assoc :
    ∀ {a b c} i j k → i < a → j < b → k < c →
    fromParts³′ a b c (i , j , k) ≡ fromParts³ a b c (i , j , k)
  fromParts-assoc {a} {b} {c} zero zero k p q r = ≡.refl
  fromParts-assoc {suc a} {suc b} {c} zero (suc j) k (Nat.s≤s p) (Nat.s≤s q) r =
    begin
      fromParts³′ (suc a) (suc b) c (0 , suc j , k)   ≡⟨⟩
      fromParts (suc b) c (suc j , k)                 ≡⟨⟩
      c + fromParts b c (j , k)                       ≡⟨ ≡.cong₂ _+_ ≡.refl (fromParts′-a-irrel b (a * suc b) c j k q r) ⟩
      c + fromParts (b + a * suc b) c (j , k)         ≡⟨⟩
      fromParts (suc (b + a * suc b)) c (suc j , k)   ≡⟨⟩
      fromParts (suc a * suc b) c (suc j , k)         ≡⟨⟩
      fromParts³ (suc a) (suc b) c (0 , suc j , k)    ∎
  fromParts-assoc {zero} {b} {c} (suc i) j k () q r
  fromParts-assoc {suc a} {b} {c} (suc i) zero k (Nat.s≤s p) q r =
    begin
      fromParts³′ (suc a) b c (suc i , 0 , k)   ≡⟨⟩
      fromParts (suc a) (b * c) (suc i , k)   ≡⟨ lem (suc a) b c (suc i) k (Nat.s≤s p) ⟩
      fromParts (suc a * b) c (suc i * b , k) ≡⟨ ≡.cong (λ h → fromParts (suc a * b) c (b + h , k)) (≡.sym (fromParts′-0 a b i p)) ⟩
      fromParts (suc a * b) c (b + fromParts a b (i , 0) , k) ≡⟨⟩
      fromParts (suc a * b) c (fromParts (suc a) b (suc i , 0) , k) ≡⟨⟩
      fromParts³ (suc a) b c (suc i , 0 , k)  ∎
  fromParts-assoc {suc a} {zero} {c} (suc i) (suc j) k p () r
  fromParts-assoc {suc a} {suc b} {c} (suc i) (suc j) k (Nat.s≤s p) q r =
    let sb = suc b
        sj = suc j
    in begin
      fromParts³′ (suc a) sb c (suc i , sj , k)                          ≡⟨⟩
      fromParts (suc a) (sb * c) (suc i , fromParts sb c (sj , k))       ≡⟨⟩
      sb * c + fromParts a (sb * c) (i , c + fromParts b c (j , k))      ≡⟨⟩
      sb * c + fromParts³′  a sb c (i , sj , k)                          ≡⟨ ≡.cong₂ _+_ ≡.refl (fromParts-assoc i sj k p q r) ⟩
      sb * c + fromParts³ a sb c (i , sj , k)                            ≡⟨⟩
      sb * c + fromParts (a * sb) c (fromParts a sb (i , sj) , k)        ≡⟨ Nat.+-assoc c _ _ ⟩
      c + (b * c + fromParts (a * sb) c (fromParts a sb (i , sj) , k))   ≡⟨ ≡.cong₂ _+_ ≡.refl (lem′ b (a * sb) c _ k) ⟩
      c + fromParts (b + a * sb) c (b + fromParts a sb (i , sj) , k)     ≡⟨⟩
      fromParts (suc a * sb) c (fromParts (suc a) sb (suc i , sj) , k)   ≡⟨⟩
      fromParts³ (suc a) sb c (suc i , sj , k) ∎

abstract
  toParts-1ˡ : ∀ {b} i → i < b → Partsℕ.toParts (constParts 1 b) i ≡ (0 , i)
  toParts-1ˡ {b} i p with Impl.compare′ i b
  toParts-1ˡ {.(suc (i + k))} i p | Impl.less .i k = ≡.refl
  toParts-1ˡ {.m} .(m + k) p | Impl.gte m k = ⊥-elim (Nat.m+n≮m m k p)

  toParts-1ʳ : ∀ {a} i → i < a → Partsℕ.toParts (constParts a 1) i ≡ (i , 0)
  toParts-1ʳ {zero} _ ()
  toParts-1ʳ {suc a} zero p = ≡.refl
  toParts-1ʳ {suc a} (suc i) (Nat.s≤s p) with Σ.≡⇒≡×≡ (toParts-1ʳ {a} i p)
  toParts-1ʳ {suc a} (suc i) (Nat.s≤s p) | q , r with Impl.compare′ i 0
  toParts-1ʳ {suc a} (suc i) (Nat.s≤s p) | q , r | Impl.gte .0 .i = Σ.≡×≡⇒≡ (≡.cong suc q , r)
