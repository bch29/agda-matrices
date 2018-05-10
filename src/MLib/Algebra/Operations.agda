open import MLib.Algebra.PropertyCode
open import MLib.Algebra.PropertyCode.Structures
  using (bimonoidCode; BimonoidK; +; *; 0#; 1#)

module MLib.Algebra.Operations {c ℓ} (struct : Struct bimonoidCode c ℓ) where

open import MLib.Prelude
open import Data.Fin.Permutation as Perm using (Permutation; Permutation′; _⟨$⟩ʳ_; _⟨$⟩ˡ_)
import Data.Fin.Permutation.Components as PC

open Struct struct
open EqReasoning setoid

--------------------------------------------------------------------------------
--  Nicer names for operations
--------------------------------------------------------------------------------

infixl 5 _+′_
infixl 6 _*′_

_+′_ = ⟦ + ⟧
_*′_ = ⟦ * ⟧
0′ = ⟦ 0# ⟧
1′ = ⟦ 1# ⟧

--------------------------------------------------------------------------------
--  Table stuff
--------------------------------------------------------------------------------

module _ {n} where
  open Setoid (Table.setoid setoid n) public
    using ()
    renaming (_≈_ to _≋_)

_≋′_ : ∀ {m n} → Table Carrier m → Table Carrier n → Set ℓ
_≋′_ = Table.Pointwise′ _≈_

open Table using (head; tail; rearrange; fromList; toList; _≗_; select)

--------------------------------------------------------------------------------
--  Operations
--------------------------------------------------------------------------------

sumₜ : ∀ {n} → Table Carrier n → Carrier
sumₜ = Table.foldr _+′_ 0′

sumₗ : List Carrier → Carrier
sumₗ = List.foldr _+′_ 0′

-- An alternative mathematical-style syntax for sumₜ

infixl 10 sumₜ-syntax

sumₜ-syntax : ∀ n → (Fin n → Carrier) → Carrier
sumₜ-syntax _ = sumₜ ∘ Table.tabulate

syntax sumₜ-syntax n (λ i → x) = ∑[ i < n ] x

--------------------------------------------------------------------------------
--  Properties
--------------------------------------------------------------------------------

-- When summing over a function from a finite set, we can pull out any value and move it to the front.
sumₜ-punchIn :
  ⦃ props : Has (associative on + ∷ commutative on + ∷ []) ⦄ →
  ∀ {n} t (i : Fin (suc n)) → sumₜ t ≈ lookup t i +′ sumₜ (Table.rearrange (Fin.punchIn i) t)
sumₜ-punchIn f zero = refl
sumₜ-punchIn {zero} t (suc ())
sumₜ-punchIn ⦃ props ⦄ {suc n} t (suc i) =
  let x = head t
      y = lookup t (suc i)
      z = sumₜ (rearrange (Fin.punchIn i) (tail t))
  in begin
    x +′ sumₜ (tail t)  ≈⟨ cong + refl (sumₜ-punchIn (tail t) i) ⟩
    x +′ (y +′ z)       ≈⟨ sym (from props (associative on +) _ _ _) ⟩
    (x +′ y) +′ z       ≈⟨ cong + (from props (commutative on +) _ _) refl ⟩
    (y +′ x) +′ z       ≈⟨ from props (associative on +) _ _ _ ⟩
    y +′ (x +′ z)       ∎

-- '_≈_' is a congruence over 'sumTable n'.
sumₜ-cong : ∀ {n} {t t′ : Table Carrier n} → t ≋ t′ → sumₜ t ≈ sumₜ t′
sumₜ-cong = Table.foldr-cong setoid (cong +)

-- A version of 'sumₜ-cong' with heterogeneous table sizes
sumₜ-cong′ : ∀ {m n} {t : Table Carrier m} {t′ : Table Carrier n} → t ≋′ t′ → sumₜ t ≈ sumₜ t′
sumₜ-cong′ {m} (≡.refl , q) = sumₜ-cong λ i → q i i ≅.refl

-- '_≡_' is a congruence over 'sum n'.
sumₜ-cong≡ : ∀ {n} {t t′ : Table Carrier n} → t ≗ t′ → sumₜ t ≡ sumₜ t′
sumₜ-cong≡ = Table.foldr-cong (≡.setoid Carrier) (≡.cong₂ _+′_)

-- The sum over the constantly zero function is zero.
sumₜ-zero :
  ⦃ props : Has₁ (0# is leftIdentity for +) ⦄ →
  ∀ n → sumₜ (Table.replicate {n} 0′) ≈ 0′
sumₜ-zero zero = refl
sumₜ-zero ⦃ props ⦄ (suc n) =
  begin
    0′ +′ sumₜ (Table.replicate {n} 0′)  ≈⟨ from props (0# is leftIdentity for +) _ ⟩
    sumₜ (Table.replicate {n} 0′)        ≈⟨ sumₜ-zero n ⟩
    0′                                   ∎

-- The '∑' operator distributes over addition.
∑-+′-hom :
  ⦃ props : Has (0# is leftIdentity for + ∷ associative on + ∷ commutative on + ∷ []) ⦄ →
  ∀ n (f g : Fin n → Carrier) → ∑[ i < n ] f i +′ ∑[ i < n ] g i ≈ ∑[ i < n ] (f i +′ g i)
∑-+′-hom ⦃ props ⦄ zero f g = from props (0# is leftIdentity for +) _
∑-+′-hom ⦃ props ⦄ (suc n) f g =
  let fz = f zero
      gz = g zero
      ∑f  = ∑[ i < n ] f (suc i)
      ∑g  = ∑[ i < n ] g (suc i)
      ∑fg = ∑[ i < n ] (f (suc i) +′ g (suc i))
  in begin
    (fz +′ ∑f) +′ (gz +′ ∑g)      ≈⟨ from props (associative on +) _ _ _ ⟩
    fz +′ (∑f +′ (gz +′ ∑g))      ≈⟨ cong + refl (sym (from props (associative on +) _ _ _)) ⟩
    fz +′ ((∑f +′ gz) +′ ∑g)      ≈⟨ cong + refl (cong + (from props (commutative on +) _ _) refl) ⟩
    fz +′ ((gz +′ ∑f) +′ ∑g)      ≈⟨ cong + refl (from props (associative on +) _ _ _) ⟩
    fz +′ (gz +′ (∑f +′ ∑g))      ≈⟨ cong + refl (cong + refl (∑-+′-hom n _ _)) ⟩
    fz +′ (gz +′ ∑fg)             ≈⟨ sym (from props (associative on +) _ _ _) ⟩
    fz +′ gz +′ ∑fg               ∎

-- The '∑' operator commutes with itself.
∑-comm :
  ⦃ props : Has (0# is leftIdentity for + ∷ associative on + ∷ commutative on + ∷ []) ⦄ →
  ∀ n m (f : Fin n → Fin m → Carrier) → ∑[ i < n ] ∑[ j < m ] f i j ≈ ∑[ j < m ] ∑[ i < n ] f i j
∑-comm ⦃ props ⦄ zero m f = sym (sumₜ-zero ⦃ narrow props ⦄ m)
∑-comm (suc n) m f =
  begin
    ∑[ j < m ] f zero j +′ ∑[ i < n ] ∑[ j < m ] f (suc i) j   ≈⟨ cong + refl (∑-comm n m _) ⟩
    ∑[ j < m ] f zero j +′ ∑[ j < m ] ∑[ i < n ] f (suc i) j   ≈⟨ ∑-+′-hom m _ _ ⟩
    ∑[ j < m ] (f zero j +′ ∑[ i < n ] f (suc i) j)            ∎

module _ ⦃ props : Has (associative on + ∷ commutative on + ∷ []) ⦄ where
  open Fin using (punchIn)
  -- Any permutation of a table has the same sum as the original.

  sumₜ-permute : ∀ {n} t (π : Permutation′ n) → sumₜ t ≈ sumₜ (rearrange (π ⟨$⟩ʳ_) t)
  sumₜ-permute {zero} t π = refl
  sumₜ-permute {suc n} t π =
    let f = lookup t
    in
    begin
      sumₜ t                                                                       ≡⟨⟩
      f 0i +′ sumₜ (rearrange (punchIn 0i) t)                                      ≈⟨ cong + refl (sumₜ-permute _ (Perm.remove (π ⟨$⟩ˡ 0i) π)) ⟩
      f 0i +′ sumₜ (rearrange (punchIn 0i ∘ (Perm.remove (π ⟨$⟩ˡ 0i) π ⟨$⟩ʳ_)) t)  ≡⟨ ≡.cong₂ _+′_ ≡.refl (sumₜ-cong≡ (≡.cong f ∘ ≡.sym ∘ Perm.punchIn-permute′ π 0i)) ⟩
      f 0i +′ sumₜ (rearrange ((π ⟨$⟩ʳ_) ∘ punchIn (π ⟨$⟩ˡ 0i)) t)                 ≡⟨ ≡.cong₂ _+′_ (≡.cong f (≡.sym (Perm.inverseʳ π))) ≡.refl ⟩
      f _  +′ sumₜ (rearrange ((π ⟨$⟩ʳ_) ∘ punchIn (π ⟨$⟩ˡ 0i)) t)                 ≈⟨ sym (sumₜ-punchIn (rearrange (π ⟨$⟩ʳ_) t) (π ⟨$⟩ˡ 0i)) ⟩
      sumₜ (rearrange (π ⟨$⟩ʳ_) t)                                                 ∎
    where
      0i = zero
      ππ0 = π ⟨$⟩ʳ (π ⟨$⟩ˡ 0i)

  -- A version of 'sumₜ-permute' allowing heterogeneous sum lengths.

  sumₜ-permute′ : ∀ {m n} t (π : Permutation m n) → sumₜ t ≈ sumₜ (rearrange (π ⟨$⟩ʳ_) t)
  sumₜ-permute′ t π with Perm.↔⇒≡ π
  sumₜ-permute′ t π | ≡.refl = sumₜ-permute t π

  ∑-permute : ∀ {n} (f : Fin n → Carrier) (π : Permutation′ n) → ∑[ i < n ] f i ≈ ∑[ i < n ] f (π ⟨$⟩ʳ i)
  ∑-permute = sumₜ-permute ∘ tabulate

  ∑-permute′ : ∀ {m n} (f : Fin n → Carrier) (π : Permutation m n) → ∑[ i < n ] f i ≈ ∑[ i < m ] f (π ⟨$⟩ʳ i)
  ∑-permute′ = sumₜ-permute′ ∘ tabulate

private
  ⌊i≟i⌋ : ∀ {n} (i : Fin n) → (i Fin.≟ i) ≡ yes ≡.refl
  ⌊i≟i⌋ i with i Fin.≟ i
  ⌊i≟i⌋ i | yes ≡.refl = ≡.refl
  ⌊i≟i⌋ i | no ¬p = ⊥-elim (¬p ≡.refl)

-- If the function takes the same value at 'i' and 'j', then swapping 'i' and
-- 'j' then selecting 'j' is the same as selecting 'i'.

select-transpose : ∀ {n} t (i j : Fin n) → lookup t i ≈ lookup t j → ∀ k → (lookup (select 0′ j t) ∘ PC.transpose i j) k ≈ lookup (select 0′ i t) k
select-transpose _ i j e k with k Fin.≟ i
select-transpose _ i j e k | yes p rewrite ≡.≡-≟-identity Fin._≟_ {j} ≡.refl = sym e
select-transpose _ i j e k | no ¬p with k Fin.≟ j
select-transpose _ i j e k | no ¬p | yes q rewrite proj₂ (≡.≢-≟-identity Fin._≟_ (¬p ∘ ≡.trans q ∘ ≡.sym)) = refl
select-transpose _ i j e k | no ¬p | no ¬q rewrite proj₂ (≡.≢-≟-identity Fin._≟_ ¬q) = refl

-- Summing over a pulse gives you the single value picked out by the pulse.

select-sum :
  ⦃ props : Has (0# is leftIdentity for + ∷ 0# is rightIdentity for + ∷ associative on + ∷ commutative on + ∷ []) ⦄ →
  ∀ {n i} (t : Table Carrier n) → sumₜ (Table.select 0′ i t) ≈ lookup t i
select-sum {zero} {()} t
select-sum ⦃ props ⦄ {suc n} {i} t =
  let f = lookup t
      open Table using (select; rearrange; replicate)
      open PC using (transpose)
  in
  begin
    sumₜ (select 0′ i t)                                                  ≈⟨ sumₜ-permute ⦃ narrow props ⦄ (select 0′ i t) (Perm.transpose zero i) ⟩
    sumₜ (rearrange (transpose zero i) (select 0′ i t))                   ≡⟨ sumₜ-cong≡ (Table.select-const 0′ i t ∘ transpose zero i) ⟩
    sumₜ (rearrange (transpose zero i) (select 0′ i (replicate (f i))))   ≈⟨ sumₜ-cong (select-transpose (replicate (f i)) zero i refl) ⟩
    sumₜ (select 0′ zero (replicate {suc n} (f i)))                       ≡⟨⟩
    f i +′ sumₜ (replicate {n} 0′)                                        ≈⟨ cong + refl (sumₜ-zero ⦃ narrow props ⦄ n) ⟩
    f i +′ 0′                                                             ≈⟨ from props (0# is rightIdentity for +) _ ⟩
    f i                                                                   ∎

sumₜ-fromList : ∀ xs → sumₜ (Table.fromList xs) ≡ sumₗ xs
sumₜ-fromList [] = ≡.refl
sumₜ-fromList (x ∷ xs) = ≡.cong₂ _+′_ ≡.refl (sumₜ-fromList xs)

sumₜ-toList : ∀ {n} (t : Table Carrier n) → sumₜ t ≡ sumₗ (Table.toList t)
sumₜ-toList {zero} _ = ≡.refl
sumₜ-toList {suc n} _ = ≡.cong₂ _+′_ ≡.refl (sumₜ-toList {n} _)

sumDistribˡ :
  ⦃ props : Has (0# is rightZero for * ∷ * ⟨ distributesOverˡ ⟩ₚ + ∷ []) ⦄ →
  ∀ {n} x (t : Table Carrier n) → x *′ sumₜ t ≈ ∑[ i < n ] (x *′ lookup t i)
sumDistribˡ ⦃ props ⦄ {Nat.zero} x f = from props (0# is rightZero for *) x
sumDistribˡ ⦃ props ⦄ {Nat.suc n} x t =
  begin
    x *′ (head t +′ sumₜ (tail t))                                    ≈⟨ from props (* ⟨ distributesOverˡ ⟩ₚ +) _ _ _ ⟩
    (x *′ head t) +′ (x *′ sumₜ (tail t))                             ≈⟨ cong + refl (sumDistribˡ x (tail t)) ⟩
    (x *′ head t) +′ sumₜ (tabulate (λ i → x *′ lookup (tail t) i))   ∎

sumDistribʳ :
  ⦃ props : Has (0# is leftZero for * ∷ * ⟨ distributesOverʳ ⟩ₚ + ∷ []) ⦄ →
  ∀ {n} x (t : Table Carrier n) → sumₜ t *′ x ≈ ∑[ i < n ] (lookup t i *′ x)
sumDistribʳ ⦃ props ⦄ {Nat.zero} x t = from props (0# is leftZero for *) x
sumDistribʳ ⦃ props ⦄ {Nat.suc n} x t =
  begin
    (head t +′ sumₜ (tail t)) *′ x                                    ≈⟨ from props (* ⟨ distributesOverʳ ⟩ₚ +) _ _ _ ⟩
    (head t *′ x) +′ (sumₜ (tail t) *′ x)                             ≈⟨ cong + refl (sumDistribʳ x (tail t)) ⟩
    (head t *′ x) +′ sumₜ (tabulate (λ i → lookup (tail t) i *′ x))   ∎
