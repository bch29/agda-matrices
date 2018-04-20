module MLib.Prelude.DFS.ViaNat where

open import MLib.Prelude
open import MLib.Prelude.Finite

open import Function.Equality using (_⟶_; _⇨_; _⟨$⟩_; cong)
open import Function.LeftInverse using (LeftInverse)

open import Data.Digit using (fromDigits; toDigits; Digit)

module _ {c p} (A-finiteSet : FiniteSet c p) where
  module A = FiniteSet A-finiteSet
  open A using () renaming (Carrier to A)

  open LeftInverse
  open Nat using (zero; suc; _^_; _+_; _*_)
  open List using ([]; _∷_)

  private
    fromBool : Bool → Digit 2
    fromBool false = Fin.zero
    fromBool true = Fin.suc Fin.zero

    toBool : Digit 2 → Bool
    toBool Fin.zero = false
    toBool (Fin.suc Fin.zero) = true
    toBool (Fin.suc (Fin.suc ()))

    toBool-fromBool : ∀ b → toBool (fromBool b) ≡ b
    toBool-fromBool false = ≡.refl
    toBool-fromBool true = ≡.refl
--     fromBinary : (n : ℕ) → List Bool → ℕ
--     fromBinary n [] = 0 -- an empty table represents an empty binary string
--     fromBinary n (x ∷ xs) = Fin.toℕ x + n * from-n-ary n xs

-- --     -- div-rem m i = "i % m" , "i / m"
--     div-rem : ∀ n → ℕ → Fin n × ℕ
--     div-rem n k = {!!}

--     to-n-ary : (n : ℕ) → ℕ → List (Fin n)
--     to-n-ary n k =
--       let r , d = div-rem n k
--           rs = to-n-ary d
--       in {!!}
--         -- r ∷ rs

-- Goal: fromDigits
-- (List.tabulate (λ x → fromBool (.i ⟨$⟩ (from A.ontoFin ⟨$⟩ x))))
-- ≡
-- fromDigits
-- (List.tabulate (λ x → fromBool (.j ⟨$⟩ (from A.ontoFin ⟨$⟩ x))))

    lookupOrElse : ∀ {n} {a} {A : Set a} → A → Fin n → List A → A
    lookupOrElse z _ [] = z
    lookupOrElse _ Fin.zero (x ∷ xs) = x
    lookupOrElse z (Fin.suc n) (x ∷ xs) = lookupOrElse z n xs

    lookupOrElse-toList : ∀ {n} {a} {A : Set a} {z : A} (i : Fin n) (t : Table A n) → lookupOrElse z i (Table.toList t) ≡ Table.lookup t i
    lookupOrElse-toList Fin.zero t = ≡.refl
    lookupOrElse-toList (Fin.suc i) = lookupOrElse-toList i ∘ Table.tail

    *2-absurd : ∀ m n → m * 2 ≡ suc (n * 2) → ⊥
    *2-absurd zero zero ()
    *2-absurd zero (suc n) ()
    *2-absurd (suc m) zero ()
    *2-absurd (suc m) (suc n) = *2-absurd m n ∘ Nat.suc-injective ∘ Nat.suc-injective

    *2-injective : ∀ m n → m * 2 ≡ n * 2 → m ≡ n
    *2-injective zero zero _ = ≡.refl
    *2-injective zero (suc n) ()
    *2-injective (suc m) zero ()
    *2-injective (suc m) (suc n) = ≡.cong suc ∘ *2-injective m n ∘ Nat.suc-injective ∘ Nat.suc-injective

    01-+-*2 : (i j : Fin 2) (m n : ℕ) → Fin.toℕ i + m * 2 ≡ Fin.toℕ j + n * 2 → m ≡ n
    01-+-*2 Fin.zero Fin.zero = *2-injective
    01-+-*2 Fin.zero (Fin.suc Fin.zero) m n = ⊥-elim ∘ *2-absurd m n
    01-+-*2 Fin.zero (Fin.suc (Fin.suc ())) m n
    01-+-*2 (Fin.suc Fin.zero) Fin.zero m n = ⊥-elim ∘ *2-absurd n m ∘ ≡.sym
    01-+-*2 (Fin.suc (Fin.suc ())) Fin.zero m n
    01-+-*2 (Fin.suc Fin.zero) (Fin.suc Fin.zero) m n = *2-injective m n ∘ Nat.suc-injective
    01-+-*2 (Fin.suc Fin.zero) (Fin.suc (Fin.suc ())) m n
    01-+-*2 (Fin.suc (Fin.suc ())) (Fin.suc Fin.zero) m n
    01-+-*2 (Fin.suc (Fin.suc ())) (Fin.suc (Fin.suc j)) m n

    +-injective₂ : ∀ m n o → o + m ≡ o + n → m ≡ n
    +-injective₂ m n zero = id
    +-injective₂ m n (suc o) = +-injective₂ m n o ∘ Nat.suc-injective

    +-injective₁ : ∀ m n o → m + o ≡ n + o → m ≡ n
    +-injective₁ m n o p = +-injective₂ m n o (≡.trans (Nat.+-comm o m) (≡.trans p (Nat.+-comm n o)))

    lookupOrElse-fromDigits : ∀ {n} (i : Fin n) (xs ys : List (Fin 2)) → fromDigits xs ≡ fromDigits ys → lookupOrElse Fin.zero i xs ≡ lookupOrElse Fin.zero i ys
    lookupOrElse-fromDigits i [] [] p = ≡.refl
    lookupOrElse-fromDigits Fin.zero [] (Fin.zero ∷ ys) p = ≡.refl
    lookupOrElse-fromDigits Fin.zero [] (Fin.suc y ∷ ys) ()
    lookupOrElse-fromDigits (Fin.suc i) [] (Fin.zero ∷ ys) p = lookupOrElse-fromDigits i [] ys (*2-injective 0 _ p)
    lookupOrElse-fromDigits (Fin.suc i) [] (Fin.suc y ∷ ys) ()
    lookupOrElse-fromDigits Fin.zero (Fin.zero ∷ xs) [] p = ≡.refl
    lookupOrElse-fromDigits Fin.zero (Fin.suc x ∷ xs) [] ()
    lookupOrElse-fromDigits {Nat.suc n} Fin.zero (x ∷ xs) (y ∷ ys) p =
      let q = 01-+-*2 x y (fromDigits xs) (fromDigits ys) p
          p′ = ≡.subst (λ fdys → Fin.toℕ x + fromDigits xs * 2 ≡ Fin.toℕ y + fdys) (≡.cong₂ _*_ (≡.sym q) ≡.refl) p
          p′′ = +-injective₁ (Fin.toℕ x) (Fin.toℕ y) _ p′
      in Fin.toℕ-injective p′′
    lookupOrElse-fromDigits (Fin.suc i) (Fin.zero ∷ xs) [] p = lookupOrElse-fromDigits i xs [] (*2-injective _ _ p)
    lookupOrElse-fromDigits (Fin.suc i) (Fin.suc x ∷ xs) [] ()
    lookupOrElse-fromDigits (Fin.suc i) (x ∷ xs) (y ∷ ys) p =
      lookupOrElse-fromDigits i xs ys (01-+-*2 x y (fromDigits xs) (fromDigits ys) p)

    toDigits-fromDigits : ∀ {n} (i : Fin n) xs → lookupOrElse Fin.zero i (proj₁ (toDigits 2 (fromDigits xs))) ≡ lookupOrElse Fin.zero i xs
    toDigits-fromDigits i xs with toDigits 2 (fromDigits xs)
    toDigits-fromDigits i xs | ds , p = lookupOrElse-fromDigits i ds xs p

  asNat : LeftInverse (FiniteSet.setoid A-finiteSet ⇨ ≡.setoid Bool) (≡.setoid ℕ)
  _⟨$⟩_ (to asNat) f = fromDigits (Table.toList (Table.map (fromBool ∘ (f ⟨$⟩_)) A.enumₜ))
  cong (to asNat) {f} p = ≡.cong fromDigits {x = Table.toList (Table.map (fromBool ∘ (f ⟨$⟩_)) A.enumₜ)} (List.tabulate-cong λ x → ≡.cong fromBool (p A.refl))
  _⟨$⟩_ (_⟨$⟩_ (from asNat) n) x = toBool (lookupOrElse Fin.zero (A.toIx x) (proj₁ (toDigits 2 n)))
  cong (_⟨$⟩_ (from asNat) n) {x} {y} = ≡.cong (λ i → toBool (lookupOrElse Fin.zero i (proj₁ (toDigits 2 n)))) ∘ cong (to A.ontoFin)
  cong (from asNat) {n} ≡.refl = cong (_⟨$⟩_ (from asNat) n)
  left-inverse-of asNat f {x} {y} p =
    begin
      toBool (lookupOrElse Fin.zero (A.toIx x) (proj₁ (toDigits 2 (fromDigits (Table.toList (Table.map (fromBool ∘ (f ⟨$⟩_)) A.enumₜ))))))
    ≡⟨ ≡.cong toBool (toDigits-fromDigits (A.toIx x) (Table.toList (Table.map (fromBool ∘ (f ⟨$⟩_)) A.enumₜ))) ⟩
      toBool (lookupOrElse Fin.zero (A.toIx x) (Table.toList (Table.map (fromBool ∘ (f ⟨$⟩_)) A.enumₜ)))
    ≡⟨ ≡.cong toBool (lookupOrElse-toList (A.toIx x) _) ⟩
      toBool (Table.lookup (Table.map (fromBool ∘ (f ⟨$⟩_)) A.enumₜ) (A.toIx x))
    ≡⟨⟩
      toBool (fromBool (f ⟨$⟩ (from A.ontoFin ⟨$⟩ (to A.ontoFin ⟨$⟩ x))))
    ≡⟨ toBool-fromBool _ ⟩
      f ⟨$⟩ (from A.ontoFin ⟨$⟩ (to A.ontoFin ⟨$⟩ x))
    ≡⟨ cong f (left-inverse-of A.ontoFin x) ⟩
      f ⟨$⟩ x
    ≡⟨ cong f p ⟩
      f ⟨$⟩ y
    ∎
    where open ≡.Reasoning
