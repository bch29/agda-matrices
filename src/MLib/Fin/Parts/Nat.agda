module MLib.Fin.Parts.Nat where

open import MLib.Prelude
open import MLib.Fin.Parts.Core

open Nat using (_*_; _+_; _<_)
open Fin using (fromℕ≤)
open Table

module Impl where
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

  fromParts : {numParts : ℕ} (parts : Table ℕ numParts) → ℕ × ℕ → ℕ
  fromParts parts (zero , j) = j
  fromParts {zero} parts (suc i , j) = 0
  fromParts {suc numParts} parts (suc i , j) = lookup parts zero + fromParts (tail parts) (i , j)

  toParts : {numParts : ℕ} (parts : Table ℕ numParts) (k : ℕ) → ℕ × ℕ
  toParts {zero} parts k = 0 , 0
  toParts {suc n} parts k with lookup parts zero | compare′ k (lookup parts zero)
  toParts {suc n} parts k | .(suc (k + k₁)) | less .k k₁ = 0 , k
  toParts {suc n} parts .(lz + k) | lz | gte .lz k =
    let i , j = toParts (tail parts) k
    in (suc i , j)

  -- Property lemmas

  +-<-lem : ∀ {a b c} → b < c → a + b < a + c
  +-<-lem {zero} p = p
  +-<-lem {suc a} p = Nat.s≤s (+-<-lem p)

  fromℕ-suc-lem : ∀ {m n} (p : m < n) → suc (fromℕ≤ p) ≡ fromℕ≤ (Nat.s≤s p)
  fromℕ-suc-lem (Nat.s≤s p) = ≡.refl

  -- Properties

  fromParts-prop : ∀ {numParts} (parts : Table ℕ numParts) {i j} → i < numParts → j < tryLookup 0 parts i → fromParts parts (i , j) < sum parts
  fromParts-prop {suc numParts} _ {zero} (Nat.s≤s p) q = Nat.≤-trans q (Nat.m≤m+n _ _)
  fromParts-prop {suc numParts} parts {suc i} (Nat.s≤s p) q = +-<-lem (fromParts-prop (tail parts) p q)

  toParts-prop : ∀ {numParts : ℕ} (parts : Table ℕ numParts) {k} → k < sum parts →
    let i , j = toParts parts k
    in Σ (i < numParts) (λ q → j < lookup parts (fromℕ≤ {i} q))
  toParts-prop {zero} parts {k} ()
  toParts-prop {suc numParts} parts {k} p with lookup parts zero | compare′ k (lookup parts zero) | ≡.inspect (lookup parts) zero
  toParts-prop {suc numParts} parts {k} p | .(suc (k + k₁)) | less .k k₁ | ≡.[ eq ] =
    Nat.s≤s Nat.z≤n ,
    Nat.≤-trans (Nat.s≤s (Nat.m≤m+n _ _)) (Nat.≤-reflexive (≡.sym eq))
  toParts-prop {suc numParts} parts {.(lz + k)} p | lz | gte .lz k | insp =
    let q , r = toParts-prop (tail parts) {k} (lz-lem _ _ _ p)
    in Nat.s≤s q , Nat.≤-trans r (Nat.≤-reflexive (≡.cong (lookup parts) (fromℕ-suc-lem _)))

  toParts-fromParts :
    {numParts : ℕ} (parts : Table ℕ numParts) (i j : ℕ) (p : j < tryLookup 0 parts i) →
    toParts parts (fromParts parts (i , j)) ≡ (i , j)
  toParts-fromParts {zero} _ i j ()
  toParts-fromParts {suc numParts} parts i j p
    with lookup parts zero
       | fromParts parts (i , j)
       | compare′ (fromParts parts (i , j)) (lookup parts zero)
       | ≡.inspect (lookup parts) zero
       | ≡.inspect (fromParts parts) (i , j)
  toParts-fromParts {suc numParts} parts zero .ipi p
    | .(suc (ipi + k)) | ipi | less .ipi k | insp₁ | ≡.[ ≡.refl ]
    = ≡.refl
  toParts-fromParts {suc numParts} parts zero .(lookup parts zero + k) p
    | .(lookup parts zero) | .(lookup parts zero + k) | gte .(lookup parts zero) k | ≡.[ ≡.refl ] | ≡.[ ≡.refl ]
    = ⊥-elim (Nat.n≮n _ (Nat.≤-trans p (Nat.m≤m+n _ k)))
  toParts-fromParts {suc numParts} parts (suc i) j p
    | .(suc (ipi + k)) | ipi | less .ipi k | ≡.[ eq ] | ≡.[ eq₁ ]
    = let y = lookup parts zero
          z = fromParts _ (i , j)
      in ⊥-elim (Nat.m≢1+m+n y {z + k} (
         begin
           y                   ≡⟨ eq ⟩
           suc (ipi + k)       ≡⟨ ≡.cong (λ h → suc (h + k)) (≡.sym eq₁) ⟩
           suc ((y + z) + k)   ≡⟨ ≡.cong suc (Nat.+-assoc y z k) ⟩
           suc (y + (z + k))   ∎))
    where open ≡.Reasoning
  toParts-fromParts {suc numParts} parts (suc i) j p
    | .(lookup parts zero) | .(lookup parts zero + k) | gte .(lookup parts zero) k | ≡.[ ≡.refl ] | ≡.[ eq₁ ]
    with Nat.+-cancelˡ-≡ (lookup parts zero) eq₁
  toParts-fromParts {suc numParts} parts (suc i) j p
    | .(lookup parts zero) | .(lookup parts zero + k) | gte .(lookup parts zero) k | ≡.[ ≡.refl ] | ≡.[ eq₁ ]
    | eq₂ rewrite ≡.sym eq₂
    = let q , r = Σ.≡⇒Pointwise-≡ (toParts-fromParts (tail parts) i j p)
      in Σ.Pointwise-≡⇒≡ (≡.cong suc q , r)

  fromParts-toParts : {numParts : ℕ} (parts : Table ℕ numParts) (k : ℕ) (p : k < sum parts) → fromParts parts (toParts parts k) ≡ k
  fromParts-toParts {zero} parts k ()
  fromParts-toParts {suc numParts} parts k p
    with lookup parts zero
       | compare′ k (lookup parts zero)
       | ≡.inspect (lookup parts) zero
  fromParts-toParts {suc numParts} parts k p | .(suc (k + k₁)) | less .k k₁ | insp = ≡.refl
  fromParts-toParts {suc numParts} parts .(lookup parts zero + k) p | .(lookup parts zero) | gte .(lookup parts zero) k | ≡.[ ≡.refl ]
    = ≡.cong₂ Nat._+_
      ≡.refl
      (fromParts-toParts (tail parts) k
        (Nat.+-cancelˡ-≤ (lookup parts zero) (Nat.≤-trans (Nat.≤-reflexive (Nat.+-suc _ k)) p)))


module Partsℕ {a} {A : Set a} {size : A → ℕ} (P : Parts A size) where
  open Parts P public

  fromParts : ℕ × ℕ → ℕ
  fromParts = Impl.fromParts partsizes

  toParts : ℕ → ℕ × ℕ
  toParts = Impl.toParts partsizes

  private
    tryLookup-lem : ∀ {i j} (p : i < numParts) → j < sizeAt (Fin.fromℕ≤ p) → j < Impl.tryLookup 0 partsizes i
    tryLookup-lem p q = Nat.≤-trans q (Nat.≤-reflexive (≡.trans (Impl.tryLookup-prop {z = 0} partsizes) (≡.cong (Impl.tryLookup 0 partsizes) (Fin.toℕ-fromℕ≤ _))))

  fromParts-prop : ∀ {i j} (p : i < numParts) → j < sizeAt (Fin.fromℕ≤ p) → fromParts (i , j) < totalSize
  fromParts-prop p = Impl.fromParts-prop _ p ∘ tryLookup-lem p

  toParts-prop : ∀ {k} → k < totalSize →
    let i , j = toParts k
    in Σ (i < numParts) (λ q → j < lookup partsizes (fromℕ≤ q))
  toParts-prop = Impl.toParts-prop _

  abstract
    toParts-fromParts : ∀ {i j} (p : i < numParts) (q : j < sizeAt (Fin.fromℕ≤ p)) → toParts (fromParts (i , j)) ≡ (i , j)
    toParts-fromParts p = Impl.toParts-fromParts partsizes _ _ ∘ tryLookup-lem p

    fromParts-toParts : ∀ k (p : k < totalSize) → fromParts (toParts k) ≡ k
    fromParts-toParts = Impl.fromParts-toParts partsizes
