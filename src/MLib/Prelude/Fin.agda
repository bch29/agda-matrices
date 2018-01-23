module MLib.Prelude.Fin where

open import MLib.Prelude.FromStdlib

open import Data.Fin public
open import Data.Fin.Properties public

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
foldUpto ℕ.zero z f = z
foldUpto (ℕ.suc n) z f = f zero (foldUpto n z (f ∘ suc))

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

data Compare′ {n} : (i j : Fin n) → Set where
  less′ : ∀ i j → i < j → Compare′ i j
  equal′ : ∀ i → Compare′ i i
  greater′ : ∀ i j → j < i → Compare′ i j

inject-< : ∀ {n} (i : Fin n) (j : Fin′ i) → inject j < i
inject-< zero ()
inject-< (suc i) zero = Nat.s≤s Nat.z≤n
inject-< (suc i) (suc j) = Nat.s≤s (inject-< i j)

compare′ : ∀ {n} (i j : Fin n) → Compare′ i j
compare′ i j with compare i j
compare′ .(inject least) j | less .j least = less′ _ _ (inject-< _ _)
compare′ i .i | equal .i = equal′ _
compare′ i .(inject least) | greater .i least = greater′ _ _ (inject-< _ _)
