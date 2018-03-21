module MLib.Prelude.Fin where

open import MLib.Prelude.FromStdlib hiding (module Σ)

open import Data.Fin public
open import Data.Fin.Properties public

open import Function.LeftInverse using (LeftInverse; _↞_)
open import Function.Equality using (_⟶_; _⟨$⟩_; cong)

import Relation.Binary.Indexed as I
import Data.Product.Relation.Pointwise.Dependent as Σ

--------------------------------------------------------------------------------
--  Types
--------------------------------------------------------------------------------

-- 'Fin∸ {n} i' is a finite set with "n - i" inhabitants.
Fin∸ : ∀ {n} → Fin n → Set
Fin∸ {n} i = Fin (n Nat.∸ toℕ i)

--------------------------------------------------------------------------------
--  Combinators
--------------------------------------------------------------------------------

foldUpto : ∀ {a} {A : Set a} n → A → (Fin n → A → A) → A
foldUpto Nat.zero z f = z
foldUpto (Nat.suc n) z f = f zero (foldUpto n z (f ∘ suc))

foldMap : ∀ {n ℓ} {A : Set ℓ} → A → (A → A → A) → (Fin n → A) → A
foldMap {n} z f g = foldUpto n z (f ∘ g)

inject∸ : ∀ {n} (i : Fin n) → Fin∸ i → Fin n
inject∸ zero j = j
inject∸ (suc i) j = inject₁ (inject∸ i j)

strengthen∸ : ∀ {n} (i : Fin n) → Fin∸ i → Fin n
strengthen∸ zero j = j
strengthen∸ (suc i) j = Fin.suc (strengthen∸ i j)

module _ where
  open import Data.List using (List; []; _∷_; _++_)
  open import Data.Maybe using (Is-just)

  -- Performs a comprehension over the finite set.
  collect : ∀ n {a} {A : Fin n → Set a} (f : ∀ i → Maybe (A i)) → List (∃ A)
  collect n {A = A} f = foldUpto n [] (λ i xs → maybe (λ x → (i , x) ∷ xs) xs (f i))

  collect′ : ∀ n {a} {A : Set a} (f : Fin n → Maybe A) → List A
  collect′ n {A = A} f = foldUpto n [] (λ i xs → maybe (λ x → x ∷ xs) xs (f i))

--------------------------------------------------------------------------------
--  Theorems
--------------------------------------------------------------------------------

module _ {ℓ p} (setoid : Setoid ℓ p) where
  open Setoid setoid renaming (Carrier to A)

  module _ {x y : A} {_+_ : A → A → A} (z-cong : x ≈ y) (+-cong : ∀ {x y u v} → x ≈ y → u ≈ v → (x + u) ≈ (y + v)) where
    foldMap-cong :
      ∀ {n}
      → (f g : Fin n → A)
      → (∀ i → f i ≈ g i)
      → foldMap {n} x _+_ f ≈ foldMap y _+_ g
    foldMap-cong {Nat.zero} f g p = z-cong
    foldMap-cong {Nat.suc n} f g p = +-cong (p _) (foldMap-cong (f ∘ suc) (g ∘ suc) (p ∘ suc))

≠-inject : ∀ n (x : Fin n) → ¬ fromℕ n ≡ inject₁ x
≠-inject .(Nat.suc _) zero ()
≠-inject .(Nat.suc _) (suc x) = ≠-inject _ x ∘ suc-injective

suc≠inject : ∀ {n} (i : Fin n) → ¬ (suc i ≡ inject₁ i)
suc≠inject zero ()
suc≠inject (suc i) p = suc≠inject i (suc-injective p)

toℕ≤n : ∀ {n} (i : Fin n) → toℕ i Nat.≤ n
toℕ≤n zero = Nat.z≤n
toℕ≤n (suc i) = Nat.s≤s (toℕ≤n i)

inject-refute : ∀ n {i : Fin (Nat.suc n)} x → i ≡ fromℕ n → ¬ i ≡ inject₁ x
inject-refute _ {zero} zero ()
inject-refute _ {zero} (suc x) ()
inject-refute Nat.zero {suc i} _()
inject-refute (Nat.suc n) {suc i} (zero) p ()
inject-refute (Nat.suc n) {suc i} (suc x) p q = inject-refute _ _ (suc-injective p) (suc-injective q)

inject-< : ∀ {n} (i : Fin n) (j : Fin′ i) → inject j < i
inject-< zero ()
inject-< (suc i) zero = Nat.s≤s Nat.z≤n
inject-< (suc i) (suc j) = Nat.s≤s (inject-< i j)

data Compareℕ {m} : (i : Fin m) (n : ℕ) → Set where
  less : ∀ bound (least : Fin′ bound) {greatest} → Compareℕ (inject! least) greatest
  equal : ∀ i → Compareℕ i (toℕ i)
  greater : ∀ greatest (least : Fin′ greatest) → Compareℕ greatest (toℕ least)

compareℕ : ∀ {m} (i : Fin m) (n : ℕ) → Compareℕ i n
compareℕ zero Nat.zero = equal _
compareℕ zero (Nat.suc n) = less (suc zero) zero
compareℕ (suc i) Nat.zero = greater (suc i) zero
compareℕ (suc i) (Nat.suc n) with compareℕ i n
compareℕ (suc .(inject! least)) (Nat.suc n) | less bound least = less (suc bound) (suc least)
compareℕ (suc i) (Nat.suc .(toℕ i)) | equal .i = equal (suc i)
compareℕ (suc i) (Nat.suc .(toℕ least)) | greater .i least = greater (suc i) (suc least)

reduce+ : ∀ m {n} (i : Fin (m Nat.+ n)) → (∃ λ (j : Fin m) → inject+ n j ≡ i) ⊎ ∃ λ j → raise m j ≡ i
reduce+ Nat.zero i = inj₂ (i , ≡.refl)
reduce+ (Nat.suc m) zero = inj₁ (zero , ≡.refl)
reduce+ (Nat.suc m) (suc i) with reduce+ m i
reduce+ (Nat.suc m) (suc i) | inj₁ (j , p) = inj₁ (suc j , ≡.cong suc p)
reduce+ (Nat.suc m) (suc i) | inj₂ (j , p) = inj₂ (j , ≡.cong suc p)

inject+-injective : ∀ {n m} {i j : Fin m} → inject+ n i ≡ inject+ n j → i ≡ j
inject+-injective {i = zero} {zero} p = ≡.refl
inject+-injective {i = zero} {suc j} ()
inject+-injective {i = suc i} {zero} ()
inject+-injective {n} {i = suc i} {suc j} p = ≡.cong suc (inject+-injective {n} (suc-injective p))

raise≢ : ∀ m n {i : Fin m} {j : Fin n} → ¬ raise n i ≡ inject+ m j
raise≢ _ _ {j = zero} ()
raise≢ _ _ {j = suc _} p = ⊥-elim (raise≢ _ _ (suc-injective p))

raise-injective : ∀ {m} n {i j : Fin m} → raise n i ≡ raise n j → i ≡ j
raise-injective Nat.zero {i} {j} p = p
raise-injective (Nat.suc n) {i} {j} p = raise-injective n (suc-injective p)

