open import MLib.Algebra.PropertyCode
open import MLib.Algebra.PropertyCode.Structures

module MLib.Matrix.Tensor {c ℓ} (struct : Struct bimonoidCode c ℓ) where

open import MLib.Prelude
open import MLib.Matrix.Core
open import MLib.Algebra.Operations struct

open Algebra using (CommutativeMonoid)
open PropertyC
open Table using (head; tail; rearrange; fromList; toList; _≗_; replicate)
open Nat using (zero; suc) renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
open Fin using (zero; suc)
open import Function.Inverse using (_↔_; Inverse)
open import Function.Equality using (_⟶_; _⟨$⟩_)
import Data.Product.Relation.Pointwise.NonDependent as ΣR

open OverBimonoid struct
open FunctionProperties

import MLib.Prelude.Fin.Pieces as P

private
  ℕsum : ∀ n → Table ℕ n → ℕ
  ℕsum _ = Table.foldr _+ℕ_ zero

  prod-sum : ∀ m n → m *ℕ n ≡ ℕsum m (replicate n)
  prod-sum zero n = ≡.refl
  prod-sum (suc m) n = ≡.cong₂ _+ℕ_ ≡.refl (prod-sum m n)

  prod-sum′ : ∀ a b c → a *ℕ b *ℕ c ≡ ℕsum (ℕsum a (replicate b)) (replicate c)
  prod-sum′ a b c =
    begin
      (a *ℕ b) *ℕ c  ≡⟨ ≡.cong₂ _*ℕ_ (prod-sum a b) ≡.refl ⟩
      (ℕsum a (replicate b)) *ℕ c  ≡⟨ prod-sum (ℕsum a (replicate b)) c ⟩
      ℕsum (ℕsum a (replicate b)) (replicate c) ∎
    where open ≡.Reasoning

  mul-pieces : ∀ m n → P.Pieces ℕ id
  mul-pieces = P.constPieces

module _ (m n : ℕ) where

  mulPieces : P.Pieces ℕ id
  mulPieces = record { numPieces = m ; pieces = replicate n }

  asPiece : (Fin m × Fin n) ↔ Fin (m *ℕ n)
  asPiece = ≡.subst (λ x → (Fin m × Fin n) ↔ Fin x) (≡.sym (prod-sum m n)) (P.asPiece mulPieces)

  intoPiece = asPiece .Inverse.to ⟨$⟩_
  fromPiece = asPiece .Inverse.from ⟨$⟩_

module _ (a b c : ℕ) where

  fromPiece³ : Fin (a *ℕ b *ℕ c) → Fin a × Fin b × Fin c
  fromPiece³ x =
    let ij , k = fromPiece (a *ℕ b) c x
        i , j = fromPiece a b ij
    in i , j , k

  intoPiece³ : Fin a × Fin b × Fin c → Fin (a *ℕ b *ℕ c)
  intoPiece³ (i , j , k) = intoPiece (a *ℕ b) c (intoPiece a b (i , j) , k)

  fromPiece³-intoPiece³ : ∀ ijk → fromPiece³ (intoPiece³ ijk) ≡ ijk
  fromPiece³-intoPiece³ (i , j , k) =
    let i′ = proj₁ (fromPiece³ (intoPiece³ (i , j , k)))
        j′ = proj₁ (proj₂ (fromPiece³ (intoPiece³ (i , j , k))))
        k′ = proj₂ (proj₂ (fromPiece³ (intoPiece³ (i , j , k))))

        rs : proj₁ (fromPiece (a *ℕ b) c (intoPiece³ (i , j , k))) ≡ intoPiece a b (i , j) ×
             k′ ≡ k
        rs = ΣR.≡⇒≡×≡ (asPiece (a *ℕ b) c .Inverse.left-inverse-of _)

        r , s = rs

        r′ : fromPiece a b (proj₁ (fromPiece (a *ℕ b) c (intoPiece³ (i , j , k)))) ≡ (i , j)
        r′ = ≡.trans (≡.cong (fromPiece a b) r) (asPiece a b .Inverse.left-inverse-of _)

        pq : i′ ≡ i × j′ ≡ j
        pq = ΣR.≡⇒≡×≡ r′

        p , q = pq

    in ΣR.≡×≡⇒≡ (p , ΣR.≡×≡⇒≡ (q , s))

  intoPiece³-fromPiece³ : ∀ i → intoPiece³ (fromPiece³ i) ≡ i
  intoPiece³-fromPiece³ x =
    let i , j , k = fromPiece³ x

        open ≡.Reasoning

        lem : intoPiece a b (i , j) ≡ proj₁ (fromPiece (a *ℕ b) c x)
        lem = begin
          intoPiece a b (i , j)                                           ≡⟨⟩
          intoPiece a b (fromPiece a b (proj₁ (fromPiece (a *ℕ b) c x)))  ≡⟨ asPiece a b .Inverse.right-inverse-of _ ⟩
          proj₁ (fromPiece (a *ℕ b) c x)                                  ∎

    in begin
      intoPiece³ (fromPiece³ x)  ≡⟨⟩
      intoPiece (a *ℕ b) c (intoPiece a b (i , j) , k) ≡⟨ ≡.cong (intoPiece (a *ℕ b) c) (ΣR.≡×≡⇒≡ (lem , ≡.refl)) ⟩
      intoPiece (a *ℕ b) c (fromPiece (a *ℕ b) c x) ≡⟨ asPiece (a *ℕ b) c .Inverse.right-inverse-of _ ⟩
      x ∎

  fromPiece³′ : Fin (a *ℕ (b *ℕ c)) → Fin a × Fin b × Fin c
  fromPiece³′ i =
    let i₁ , i₂₃ = fromPiece a (b *ℕ c) i
        i₂ , i₃ = fromPiece b c i₂₃
    in i₁ , i₂ , i₃

  intoPiece³′ : Fin a × Fin b × Fin c → Fin (a *ℕ (b *ℕ c))
  intoPiece³′ (i , j , k) = intoPiece a (b *ℕ c) (i , intoPiece b c (j , k))

  fromPiece³′-intoPiece³′ : ∀ ijk → fromPiece³′ (intoPiece³′ ijk) ≡ ijk
  fromPiece³′-intoPiece³′ (i , j , k) =
    let i′ = proj₁ (fromPiece³′ (intoPiece³′ (i , j , k)))
        j′ = proj₁ (proj₂ (fromPiece³′ (intoPiece³′ (i , j , k))))
        k′ = proj₂ (proj₂ (fromPiece³′ (intoPiece³′ (i , j , k))))

        p , q = ΣR.≡⇒≡×≡ (asPiece a (b *ℕ c) .Inverse.left-inverse-of _)
        q′ = ≡.trans (≡.cong (fromPiece b c) q) (asPiece b c .Inverse.left-inverse-of _)

    in ΣR.≡×≡⇒≡ (p , q′)

  intoPiece-assoc : ∀ ijk → ≡.subst Fin (Nat.*-assoc a b c) (intoPiece³ ijk) ≡ intoPiece³′ ijk
  intoPiece-assoc (i , j , k) = {!!}
    -- let lem₁ : ≡.subst Fin (Nat.*-assoc a b c) (intoPiece a (b *ℕ c) (i , ?)) ≡ intoPiece (a *ℕ b) c (? , k)
    --     lem₁ = ?
    -- in ?

  fromPiece-assoc : (i : Fin (a *ℕ b *ℕ c)) → fromPiece³ i ≡ fromPiece³′ (≡.subst Fin (Nat.*-assoc a b c) i)
  fromPiece-assoc i =
    begin
      fromPiece³ i                               ≡⟨ ≡.sym (fromPiece³′-intoPiece³′ _) ⟩
      fromPiece³′ (intoPiece³′ (fromPiece³ i))   ≡⟨ ≡.cong fromPiece³′ (≡.sym (intoPiece-assoc _)) ⟩
      fromPiece³′ (≡.subst Fin (Nat.*-assoc a b c) (intoPiece³ (fromPiece³ i)))   ≡⟨ ≡.cong (fromPiece³′ ∘ ≡.subst Fin (Nat.*-assoc a b c)) (intoPiece³-fromPiece³ _) ⟩
      fromPiece³′ (≡.subst Fin (Nat.*-assoc a b c) i)   ∎
    where open ≡.Reasoning

module Defn {m n p q : ℕ} where
  -- Tensor product

  _⊠_ : Matrix S m n → Matrix S p q → Matrix S (m Nat.* p) (n Nat.* q)
  (A ⊠ B) i j =
    let i₁ , i₂ = fromPiece m p i
        j₁ , j₂ = fromPiece n q j
    in A i₁ j₁ *′ B i₂ j₂

-- open Defn using (_⊠_) public

-- module _ ⦃ props : Has (associative on * ∷ []) ⦄ {m n p q r s} where
--   open _≃_

--   ⊠-associative :
--     (A : Matrix S m n) (B : Matrix S p q) (C : Matrix S r s) →
--     (A ⊠ B) ⊠ C ≃ A ⊠ (B ⊠ C)
--   ⊠-associative A B C .m≡p = Nat.*-assoc m p r
--   ⊠-associative A B C .n≡q = Nat.*-assoc n q s
--   ⊠-associative A B C .equal i j =
--     let i₁₂ , i₃ = fromPiece (mul-pieces (m Nat.* p) r) (≡.subst Fin (prod-sum (m Nat.* p) r) i)
--         i₁ , i₂ = fromPiece (mul-pieces m p) (≡.subst Fin (prod-sum m p) i₁₂)

--         j₁₂ , j₃ = fromPiece (mul-pieces (n Nat.* q) s) (≡.subst Fin (prod-sum (n Nat.* q) s) j)
--         j₁ , j₂ = fromPiece (mul-pieces n q) (≡.subst Fin (prod-sum n q) j₁₂)

--         i′ = ≡.subst Fin (Nat.*-assoc m p r) i
--         j′ = ≡.subst Fin (Nat.*-assoc n q s) j

--         i′₁ , i′₂₃ = fromPiece (mul-pieces m (p Nat.* r)) (≡.subst Fin (prod-sum m (p Nat.* r)) i′)
--         i′₂ , i′₃ = fromPiece (mul-pieces p r) (≡.subst Fin (prod-sum p r) i′₂₃)

--         j′₁ , j′₂₃ = fromPiece (mul-pieces n (q Nat.* s)) (≡.subst Fin (prod-sum n (q Nat.* s)) j′)
--         j′₂ , j′₃ = fromPiece (mul-pieces q s) (≡.subst Fin (prod-sum q s) j′₂₃)

--         -- i′′ = intoPiece (mul-pieces m (p Nat.* r)) i₁ (≡.subst Fin (≡.sym (prod-sum p r)) (intoPiece (mul-pieces p r) i₂ i₃))

--         open EqReasoning S.setoid
--     in begin
--       ((A ⊠ B) ⊠ C) i j              ≡⟨⟩
--       A i₁ j₁ *′ B i₂ j₂ *′ C i₃ j₃   ≈⟨ from props (associative on *) _ _ _ ⟩
--       A i₁ j₁ *′ (B i₂ j₂ *′ C i₃ j₃) ≈⟨ {!!} ⟩
--       A i′₁ j′₁ *′ (B i′₂ j′₂ *′ C i′₃ j′₃) ≡⟨⟩
--       (A ⊠ (B ⊠ C)) i′ j′ ∎
