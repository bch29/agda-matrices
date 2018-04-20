open import MLib.Algebra.PropertyCode
open import MLib.Algebra.PropertyCode.Structures
  using (bimonoidCode; BimonoidK)
  renaming (+ to ⊕; * to ⊛; 0# to 0●; 1# to 1●)

module MLib.Algebra.Operations {c ℓ} (struct : Struct bimonoidCode c ℓ) where

open import Function.Inverse using (Inverse; _↔_)
open import Function.Equality using (_⟨$⟩_)

open import MLib.Prelude
open Nat using (zero; suc)
open Fin using (zero; suc)
open PropertyC

open Struct struct
open EqReasoning setoid

--------------------------------------------------------------------------------
--  Nicer names for operations
--------------------------------------------------------------------------------

infixl 5 _+_
infixl 6 _*_

_+_ = ⟦ ⊕ ⟧
_*_ = ⟦ ⊛ ⟧
0# = ⟦ 0● ⟧
1# = ⟦ 1● ⟧

--------------------------------------------------------------------------------
--  Table stuff
--------------------------------------------------------------------------------

module _ {n} where
  open Setoid (Table.setoid setoid n) public
    using ()
    renaming (_≈_ to _≋_)

open Table using (head; tail; rearrange; fromList; toList; _≗_)

--------------------------------------------------------------------------------
--  Operations
--------------------------------------------------------------------------------

sumₜ : ∀ {n} → Table Carrier n → Carrier
sumₜ = Table.foldr _+_ 0#

sumₗ : List Carrier → Carrier
sumₗ = List.foldr _+_ 0#

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
  ⦃ props : Has (associative on ⊕ ∷ commutative on ⊕ ∷ []) ⦄ →
  ∀ {n} t (i : Fin (suc n)) → sumₜ t ≈ lookup t i + sumₜ (Table.rearrange (Fin.punchIn i) t)
sumₜ-punchIn f zero = refl
sumₜ-punchIn {zero} t (suc ())
sumₜ-punchIn ⦃ props ⦄ {suc n} t (suc i) =
  begin
    head t + sumₜ (tail t)                                                    ≈⟨ cong ⊕ refl (sumₜ-punchIn (tail t) i) ⟩
    head t + (lookup t (suc i) + sumₜ (rearrange (Fin.punchIn i) (tail t)))   ≈⟨ sym (from props (associative on ⊕) _ _ _) ⟩
    (head t + lookup t (suc i)) + sumₜ (rearrange (Fin.punchIn i) (tail t))   ≈⟨ cong ⊕ (from props (commutative on ⊕) _ _) refl ⟩
    (lookup t (suc i) + head t) + sumₜ (rearrange (Fin.punchIn i) (tail t))   ≈⟨ from props (associative on ⊕) _ _ _ ⟩
    lookup t (suc i) + (head t + sumₜ (rearrange (Fin.punchIn i) (tail t)))   ∎

-- '_≈_' is a congruence over 'sumTable n'.
sumₜ-cong : ∀ {n} {t t′ : Table Carrier n} → t ≋ t′ → sumₜ t ≈ sumₜ t′
sumₜ-cong {zero} p = refl
sumₜ-cong {suc n} p = cong ⊕ (p _) (sumₜ-cong (p ∘ suc))

-- '_≡_' is a congruence over 'sum n'.
sumₜ-cong≡ : ∀ {n} {t t′ : Table Carrier n} → t ≗ t′ → sumₜ t ≡ sumₜ t′
sumₜ-cong≡ {zero} p = ≡.refl
sumₜ-cong≡ {suc n} p = ≡.cong₂ _+_ (p _) (sumₜ-cong≡ (p ∘ suc))

-- The sum over the constantly zero function is zero.
sumₜ-zero :
  ⦃ props : Has₁ (0● is leftIdentity for ⊕) ⦄ →
  ∀ n → sumₜ (Table.replicate {n} 0#) ≈ 0#
sumₜ-zero zero = refl
sumₜ-zero ⦃ props ⦄ (suc n) =
  begin
    0# + sumₜ (Table.replicate {n} 0#)  ≈⟨ from props (0● is leftIdentity for ⊕) _ ⟩
    sumₜ (Table.replicate {n} 0#)       ≈⟨ sumₜ-zero n ⟩
    0#                                  ∎

-- The '∑' operator distributes over addition.
∑-+-hom :
  ⦃ props : Has (0● is leftIdentity for ⊕ ∷ associative on ⊕ ∷ commutative on ⊕ ∷ []) ⦄ →
  ∀ n (f g : Fin n → Carrier) → ∑[ i < n ] f i + ∑[ i < n ] g i ≈ ∑[ i < n ] (f i + g i)
∑-+-hom ⦃ props ⦄ zero f g = from props (0● is leftIdentity for ⊕) _
∑-+-hom ⦃ props ⦄ (suc n) f g =
  let fz = f zero
      gz = g zero
      ∑f  = ∑[ i < n ] f (suc i)
      ∑g  = ∑[ i < n ] g (suc i)
      ∑fg = ∑[ i < n ] (f (suc i) + g (suc i))
  in begin
    (fz + ∑f) + (gz + ∑g)      ≈⟨ from props (associative on ⊕) _ _ _ ⟩
    fz + (∑f + (gz + ∑g))      ≈⟨ cong ⊕ refl (sym (from props (associative on ⊕) _ _ _)) ⟩
    fz + ((∑f + gz) + ∑g)      ≈⟨ cong ⊕ refl (cong ⊕ (from props (commutative on ⊕) _ _) refl) ⟩
    fz + ((gz + ∑f) + ∑g)      ≈⟨ cong ⊕ refl (from props (associative on ⊕) _ _ _) ⟩
    fz + (gz + (∑f + ∑g))      ≈⟨ cong ⊕ refl (cong ⊕ refl (∑-+-hom n _ _)) ⟩
    fz + (gz + ∑fg)            ≈⟨ sym (from props (associative on ⊕) _ _ _) ⟩
    fz + gz + ∑fg              ∎

-- The '∑' operator commutes with itself.
∑-comm :
  ⦃ props : Has (0● is leftIdentity for ⊕ ∷ associative on ⊕ ∷ commutative on ⊕ ∷ []) ⦄ →
  ∀ n m (f : Fin n → Fin m → Carrier) → ∑[ i < n ] ∑[ j < m ] f i j ≈ ∑[ j < m ] ∑[ i < n ] f i j
∑-comm ⦃ props ⦄ zero m f = sym (sumₜ-zero ⦃ narrow props ⦄ m)
∑-comm (suc n) m f =
  begin
    ∑[ j < m ] f zero j + ∑[ i < n ] ∑[ j < m ] f (suc i) j   ≈⟨ cong ⊕ refl (∑-comm n m _) ⟩
    ∑[ j < m ] f zero j + ∑[ j < m ] ∑[ i < n ] f (suc i) j   ≈⟨ ∑-+-hom m _ _ ⟩
    ∑[ j < m ] (f zero j + ∑[ i < n ] f (suc i) j)            ∎

module _ ⦃ props : Has (associative on ⊕ ∷ commutative on ⊕ ∷ []) ⦄ where
  open Fin using (punchIn; removeIn↔)
  -- Any permutation of a table has the same sum as the original.

  sumₜ-permute : ∀ {n} t (π : Fin n ↔ Fin n) → sumₜ t ≈ sumₜ (rearrange (Inverse.to π ⟨$⟩_) t)
  sumₜ-permute {zero} t π = refl
  sumₜ-permute {suc n} t π =
    let f = lookup t
    in
    begin
      sumₜ t                                                                                            ≡⟨⟩
      f 0i + sumₜ (rearrange (punchIn 0i) t)                                                            ≈⟨ cong ⊕ refl (sumₜ-permute _ (removeIn↔ (Inverse.from π ⟨$⟩ 0i) π)) ⟩
      f 0i + sumₜ (rearrange (punchIn 0i ∘ (Inverse.to (removeIn↔ (Inverse.from π ⟨$⟩ 0i) π) ⟨$⟩_)) t)  ≡⟨ ≡.cong₂ _+_ ≡.refl (sumₜ-cong≡ (≡.cong f ∘ ≡.sym ∘ Fin.punchIn-permute′ π 0i)) ⟩
      f 0i + sumₜ (rearrange ((Inverse.to π ⟨$⟩_) ∘ punchIn (Inverse.from π ⟨$⟩ 0i)) t)                 ≡⟨ ≡.cong₂ _+_ (≡.cong f (≡.sym (Inverse.right-inverse-of π _))) ≡.refl ⟩
      f _  + sumₜ (rearrange ((Inverse.to π ⟨$⟩_) ∘ punchIn (Inverse.from π ⟨$⟩ 0i)) t)                 ≈⟨ sym (sumₜ-punchIn (rearrange (Inverse.to π ⟨$⟩_) t) (Inverse.from π ⟨$⟩ 0i)) ⟩
      sumₜ (rearrange (Inverse.to π ⟨$⟩_) t)                                                            ∎
    where
      0i = zero
      ππ0 = Inverse.to π ⟨$⟩ (Inverse.from π ⟨$⟩ 0i)

  -- A version of 'sumₜ-permute' allowing heterogeneous sum lengths.

  sumₜ-permute′ : ∀ {m n} t (π : Fin m ↔ Fin n) → sumₜ t ≈ sumₜ (rearrange (Inverse.to π ⟨$⟩_) t)
  sumₜ-permute′ t π with Fin.↔-≡ π
  sumₜ-permute′ t π | ≡.refl = sumₜ-permute t π

  ∑-permute : ∀ {n} (f : Fin n → Carrier) (π : Fin n ↔ Fin n) → ∑[ i < n ] f i ≈ ∑[ i < n ] f (Inverse.to π ⟨$⟩ i)
  ∑-permute = sumₜ-permute ∘ tabulate

  ∑-permute′ : ∀ {m n} (f : Fin n → Carrier) (π : Fin m ↔ Fin n) → ∑[ i < n ] f i ≈ ∑[ i < m ] f (Inverse.to π ⟨$⟩ i)
  ∑-permute′ = sumₜ-permute′ ∘ tabulate

private
  ⌊i≟i⌋ : ∀ {n} (i : Fin n) → (i Fin.≟ i) ≡ yes ≡.refl
  ⌊i≟i⌋ i with i Fin.≟ i
  ⌊i≟i⌋ i | yes ≡.refl = ≡.refl
  ⌊i≟i⌋ i | no ¬p = ⊥-elim (¬p ≡.refl)

-- If the function takes the same value at 'i' and 'j', then swapping 'i' and
-- 'j' then selecting 'j' is the same as selecting 'i'.

select-swap : ∀ {n} t (i j : Fin n) → lookup t i ≈ lookup t j → ∀ k → (lookup (Table.select 0# j t) ∘ Fin.swapFin i j) k ≈ lookup (Table.select 0# i t) k
select-swap _ i j e k with k Fin.≟ j
select-swap _ i j e k | yes p with k Fin.≟ i
select-swap _ .k .k e k | yes ≡.refl | yes ≡.refl rewrite ⌊i≟i⌋ k = refl
select-swap _ i .k e k | yes ≡.refl | no ¬q with i Fin.≟ k
select-swap _ i .k e k | yes ≡.refl | no ¬q | yes p = ⊥-elim (¬q (≡.sym p))
select-swap _ i .k e k | yes ≡.refl | no ¬q | no ¬p = refl
select-swap _ i j e k | no ¬p with k Fin.≟ i
select-swap t i j e k | no ¬p | yes q rewrite ⌊i≟i⌋ j = sym e
select-swap _ i j e k | no ¬p | no ¬q with k Fin.≟ j
select-swap _ i j e k | no ¬p | no ¬q | yes p = ⊥-elim (¬p p)
select-swap _ i j e k | no ¬p | no ¬q | no ¬r = refl

sumₜ-fromList : ∀ xs → sumₜ (Table.fromList xs) ≡ sumₗ xs
sumₜ-fromList [] = ≡.refl
sumₜ-fromList (x ∷ xs) = ≡.cong₂ _+_ ≡.refl (sumₜ-fromList xs)

sumₜ-toList : ∀ {n} (t : Table Carrier n) → sumₜ t ≡ sumₗ (Table.toList t)
sumₜ-toList {zero} _ = ≡.refl
sumₜ-toList {suc n} _ = ≡.cong₂ _+_ ≡.refl (sumₜ-toList {n} _)
