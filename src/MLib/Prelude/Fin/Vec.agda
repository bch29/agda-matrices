module MLib.Prelude.Fin.Vec where

import Data.List as List
import Data.List.Properties as List
open import Data.List using (List; _∷_; [])
import Data.Product as Product

open import MLib.Prelude.FromStdlib
open import MLib.Prelude.Fin
open import MLib.Prelude.Paths
open import MLib.Permutations

Vec : ∀ {a} (A : Set a) → ℕ → Set a
Vec A n = Fin n → A

module _ {a} {A : Set a} where

  Vec-setoid : ∀ n → Setoid _ _
  Vec-setoid n = Fin n →-setoid A

--------------------------------------------------------------------------------
--  List conversion
--------------------------------------------------------------------------------

  toList : ∀ {n} → Vec A n → List A
  toList {Nat.zero} f = []
  toList {Nat.suc n} f = f zero ∷ toList (f ∘ suc)

  toList′ : ∃ (Vec A) → List A
  toList′ (_ , f) = toList f

  fromList : (xs : List A) → Vec A (List.length xs)
  fromList [] ()
  fromList (x ∷ xs) zero = x
  fromList (x ∷ xs) (suc i) = fromList xs i

  fromList′ : List A → ∃ (Vec A)
  fromList′ xs = List.length xs , fromList xs

  fromList′-toList : ∀ {n} (f : Vec A n) → OverΣ _≗_ (fromList′ (toList f)) (n , f)
  fromList′-toList {ℕ.zero} f = ≡.refl , λ ()
  fromList′-toList {ℕ.suc n} f = Pointwise.liftPseudoInjOver decideFin ≡.refl (fromList′-toList (f ∘ suc))
    where
      decideFin : ∀ {n} (i : Fin (ℕ.suc n)) → i ≡ zero ⊎ ∃ λ j → i ≡ suc j
      decideFin zero = inj₁ ≡.refl
      decideFin (suc i) = inj₂ (i , ≡.refl)

  fromList′-toList′ : (x : ∃ (Vec A)) → OverΣ _≗_ (fromList′ (toList′ x)) x
  fromList′-toList′ (_ , f) = fromList′-toList f

  toList-length : ∀ {n} (f : Vec A n) → List.length (toList f) ≡ n
  toList-length = proj₁ ∘ fromList′-toList

  toList-fromList : (xs : List A) → toList (fromList xs) ≡ xs
  toList-fromList [] = ≡.refl
  toList-fromList (x ∷ xs) = ≡.cong₂ _∷_ ≡.refl (toList-fromList xs)

--------------------------------------------------------------------------------
--  Select
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
--  Split and append
--------------------------------------------------------------------------------

  splitList : (xs : List A) → ℕ → List A × List A
  splitList [] _ = [] , []
  splitList (x ∷ xs) Nat.zero = [] , x ∷ xs
  splitList (x ∷ xs) (Nat.suc i) with splitList xs i
  splitList (x ∷ xs) (Nat.suc i) | ys , zs = x ∷ ys , zs

  -- Split 'f' into two vectors: those values up to and not including 'i' and
  -- those values after and including 'i'.
  splitVecL : ∀ {n} (i : Fin n) → Vec A n → ∃ (Vec A) × ∃ (Vec A)
  splitVecL i f with splitList (toList f) (toℕ i)
  splitVecL i f | xs , ys = fromList′ xs , fromList′ ys

  splitList-length₁ : ∀ (xs : List A) (i : Fin (List.length xs)) → List.length (proj₁ (splitList xs (toℕ i))) ≡ toℕ i
  splitList-length₁ [] ()
  splitList-length₁ (x ∷ xs) zero = ≡.refl
  splitList-length₁ (x ∷ xs) (suc i) = ≡.cong Nat.suc (splitList-length₁ xs i)

  splitList-length₂ : ∀ (xs : List A) (i : ℕ) → List.length (proj₂ (splitList xs i)) ≡ List.length xs Nat.∸ i
  splitList-length₂ [] ℕ.zero = ≡.refl
  splitList-length₂ [] (ℕ.suc i) = ≡.refl
  splitList-length₂ (x ∷ xs) ℕ.zero = ≡.refl
  splitList-length₂ (x ∷ xs) (ℕ.suc i) = splitList-length₂ xs i

  splitVec : ∀ {n} (i : Fin n) → Vec A n → ((Fin′ i → A) × (Fin∸ i → A))
  splitVec i f with toList f | toList-length f
  splitVec i f | xs | ≡.refl with splitList xs (toℕ i) | splitList-length₁ xs i | splitList-length₂ xs (toℕ i)
  splitVec i f | xs | ≡.refl | ys , zs | p | q with fromList ys | fromList zs
  splitVec i f | xs | ≡.refl | ys , zs | p | q | g | h =
    ≡.subst (λ m → Fin m → A) p g ,
    ≡.subst (λ m → Fin m → A) q h

  splitVec′ : ∀ {n} (i : Fin n) → Vec A n → ∃ (Vec A) × ∃ (Vec A)
  splitVec′ i f with splitVec i f
  splitVec′ i f | g , h = (_ , g) , (_ , h)

  splitVecL-splitVec : ∀ {n} (i : Fin n) (f : Vec A n) →
    let u , v = splitVecL i f
        u′ , v′ = splitVec′ i f
    in OverΣ _≗_ u u′ × OverΣ _≗_ v v′
  splitVecL-splitVec i f with toList f | toList-length f
  splitVecL-splitVec i f | xs | ≡.refl with splitList xs (toℕ i) | splitList-length₁ xs i | splitList-length₂ xs (toℕ i)
  splitVecL-splitVec i f | xs | ≡.refl | ys , zs | p | q with fromList ys | fromList zs
  splitVecL-splitVec {n} i f | xs | ≡.refl | ys , zs | p | q | g | h =
    OverΣ.subst p (λ x → ≡.refl) , OverΣ.subst q (λ x → ≡.refl)

  appVecL : ∀ {m n} → (Vec A m) → (Vec A n) → ∃ (Vec A)
  appVecL f g = fromList′ (toList f List.++ toList g)

  appVecL′ : ∃ (Vec A) → ∃ (Vec A) → ∃ (Vec A)
  appVecL′ u v = fromList′ (toList′ u List.++ toList′ v)

  appVec-length : ∀ {m n} (f : Vec A m) (g : Vec A n) → proj₁ (appVecL f g) ≡ m Nat.+ n
  appVec-length f g with toList-length f | toList-length g | toList f List.++ toList g | List.length-++ (toList f) {toList g}
  appVec-length f g | p | q | xs | lpp with fromList xs
  appVec-length f g | p | q | xs | lpp | _ = ≡.trans lpp (≡.cong₂ Nat._+_ p q)

  appVec : ∀ {m n} (f : Vec A m) (g : Vec A n) → (Vec A (m Nat.+ n))
  appVec f g = ≡.subst (λ o → Fin o → A) (appVec-length f g) (fromList (toList f List.++ toList g))

  appVec′ : ∀ {m n} (f : Vec A m) (g : Vec A n) → ∃ (Vec A)
  appVec′ f g = _ , appVec f g

  appVec′′ : ∃ (Vec A) → ∃ (Vec A) → ∃ (Vec A)
  appVec′′ (_ , f) (_ , g) = _ , appVec f g

  appVecL-appVec : ∀ {m n} (f : Vec A m) (g : Vec A n) → OverΣ _≗_ (appVecL f g) (appVec′ f g)
  appVecL-appVec f g =
    let p = appVec-length f g
    in OverΣ.subst p λ _ → ≡.refl

  ++-splitList : ∀ {xs : List A} (i : ℕ) → xs ≡ uncurry List._++_ (splitList xs i)
  ++-splitList {[]} n = ≡.refl
  ++-splitList {x ∷ xs} Nat.zero = ≡.refl
  ++-splitList {x ∷ xs} (Nat.suc i) = ≡.cong (x ∷_) (++-splitList i)

  fromList-cong : ∀ {xs ys : List A} → xs ≡ ys → OverΣ _≗_ (fromList′ xs) (fromList′ ys)
  fromList-cong p = Setoid.reflexive (Pointwise.pairSetoid ℕ Fin (λ _ → A)) (≡.cong fromList′ p)

  splitList-splitVec : ∀ {n} {f : Vec A n} (i : Fin n) → splitList (toList′ (n , f)) (toℕ i) ≡ Product.map toList′ toList′ (splitVecL i f)
  splitList-splitVec {f = f} i =
    let ys , zs = splitList (toList f) (toℕ i)
    in ≡.sym (≡.cong₂ _,_ (toList-fromList ys) (toList-fromList zs))

  PS = Pointwise.pairSetoid ℕ Fin (λ _ → A)
  module PS = Setoid PS

  app-split₁ : ∀ {n} (i : Fin n) (f : Vec A n) → OverΣ _≗_ (n , f) (uncurry appVecL′ (splitVecL i f))
  app-split₁ {n} i f =
    begin
      n , f                                                                        ≈⟨ PS.sym (fromList′-toList′ _) ⟩
      fromList′ (toList′ (n , f))                                                  ≈⟨ fromList-cong {toList′ (n , f)} (++-splitList (toℕ i)) ⟩
      fromList′ (uncurry List._++_ (splitList (toList′ (n , f)) (toℕ i)))          ≈⟨ PS.reflexive (≡.cong (fromList′ ∘ uncurry List._++_) (splitList-splitVec i)) ⟩
      fromList′ (uncurry List._++_ (Product.map toList′ toList′ (splitVecL i f)))  ≡⟨⟩
      uncurry appVecL′ (splitVecL i f)                                             ∎
    where
      open EqReasoning PS

  -- ≐-toList : ∀ {n} {f g : Vec A n} → f ≗ g → toList f ≡ toList g
  -- ≐-toList p = {!!}

  -- appVecL-cong : {u u′ v v′ : ∃ (Vec A)} → OverΣ _≗_ u u′ → OverΣ _≗_ v v′ → OverΣ _≗_ (appVecL′ u v) (appVecL′ u′ v′)
  -- appVecL-cong {u} {u′} {v} {v′} (≡.refl , r) (≡.refl , s) =
  --   let p = ≡.cong (proj₁ ∘ fromList′) (≡.cong₂ List._++_ (≐-toList r) (≐-toList s))
  --   in p , {!!}
    -- Pointwise.cong _ 

  -- app-split₂ : ∀ {n} (i : Fin n) (f : Vec A n) → OverΣ _≗_ (uncurry appVecL′ (splitVecL i f)) (uncurry appVec′ (splitVec i f))
  -- app-split₂ i f =
  --   begin
  --     uncurry appVecL′ (splitVecL i f)                                ≡⟨⟩
  --     uncurry appVecL′ (splitVecL i f .proj₁ , splitVecL i f .proj₂)  ≈⟨ {!!} ⟩
  --     uncurry appVecL′ (splitVecL i f .proj₁ , splitVec′ i f .proj₂)  ≈⟨ {!!} ⟩
  --     uncurry appVecL′ (splitVec′ i f)                                ≡⟨⟩
  --     uncurry appVecL (splitVec i f)                                  ≈⟨ appVecL-appVec (splitVec i f .proj₁) _ ⟩
  --     uncurry appVec′ (splitVec i f)                                  ∎
  --   where
  --     open EqReasoning PS

  -- app-split : ∀ {n} (i : Fin n) (f : Vec A n) → OverΣ _≗_ (n , f) (uncurry appVec′ (splitVec i f))
  -- app-split {n} i f =
  --   begin
  --     n , f                               ≈⟨ app-split′ i f ⟩
  --     uncurry appVecL′ (splitVecL i f)    ≈⟨ {!!} ⟩
  --     uncurry appVec′′ (splitVecL i f)    ≈⟨ {!!} ⟩
  --     uncurry appVec′ (splitVec i f)      ∎
  --   where
  --     PS = Pointwise.pairSetoid ℕ Fin (λ _ → A)
  --     module PS = Setoid PS
  --     open EqReasoning PS
