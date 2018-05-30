module MLib.Fin.Parts.Simple where

open import MLib.Prelude
open import MLib.Fin.Parts.Core
open import MLib.Fin.Parts
open import MLib.Fin.Parts.Nat
import MLib.Fin.Parts.Nat.Simple as PNS

open Nat using (_*_; _+_; _<_)
open Fin using (toℕ; fromℕ≤)
open Table

open PNS using (sum-replicate-*; repl)

asParts : ∀ {a b} → Fin (a * b) ↔ (Fin a × Fin b)
asParts {a} {b} = ≡.subst (λ n → Fin n ↔ (Fin a × Fin b)) (sum-replicate-* a b) (Parts.asParts (constParts a b))

fromParts : ∀ {a b} → Fin a × Fin b → Fin (a * b)
fromParts = Inverse.from asParts ⟨$⟩_

toParts : ∀ {a b} → Fin (a * b) → Fin a × Fin b
toParts = Inverse.to asParts ⟨$⟩_

fromParts³′ : ∀ {a b c} → Fin a × Fin b × Fin c → Fin (a * (b * c))
fromParts³′ {a} {b} {c} (i , j , k) = fromParts (i , fromParts (j , k))

fromParts³ : ∀ {a b c} → Fin a × Fin b × Fin c → Fin (a * b * c)
fromParts³ {a} {b} {c} (i , j , k) = fromParts (fromParts (i , j) , k)

private
  fromParts′ : ∀ {a b} → Fin a × Fin b → Fin (sum (repl a b))
  fromParts′ {a} {b} = Parts.fromParts (constParts a b)

  toParts′ : ∀ {a b} → Fin (sum (repl a b)) → Fin a × Fin b
  toParts′ {a} {b} = Parts.toParts (constParts a b)

  asParts-prop : ∀ {a b} → asParts {a} {b} ≅ Parts.asParts (constParts a b)
  asParts-prop {a} {b} = ≅.≡-subst-removable _ _ _

  abstract
    fromParts′-prop : ∀ {a b} (ij : Fin a × Fin b) → toℕ (fromParts ij) ≡ toℕ (fromParts′ ij)
    fromParts′-prop {a} {b} ij =
      ≅.≅-to-≡ (≅.icong (λ n → Fin n ↔ (Fin a × Fin b))
                         (≡.sym (sum-replicate-* a b))
                         (λ {n} (ap : Fin n ↔ (Fin a × Fin b)) → toℕ (Inverse.from ap ⟨$⟩ ij))
                         asParts-prop)

    toParts′-prop : ∀ {a b} {x : Fin (a * b)} {x′ : Fin (sum (repl a b))} → x ≅ x′ → Σ.map toℕ toℕ (toParts {a} x) ≡ Σ.map toℕ toℕ (toParts′ {a} x′)
    toParts′-prop {a} {b} {x} {x′} x≅x′ =
      ≅.≅-to-≡ (≅.icong₂
        (λ n → Fin n ↔ (Fin a × Fin b))
        (≡.sym (sum-replicate-* a b))
        (λ {n} (ap : Fin n ↔ (Fin a × Fin b)) x → Σ.map toℕ toℕ (Inverse.to ap ⟨$⟩ x))
        asParts-prop
        x≅x′)

    fromParts³′-prop : ∀ {a b c} (i : Fin a) (j : Fin b) (k : Fin c) → toℕ (fromParts³′ (i , j , k)) ≡ PNS.fromParts³′ a b c (toℕ i , toℕ j , toℕ k)
    fromParts³′-prop {a} {b} {c} i j k =
      begin
        toℕ (fromParts (i , fromParts (j , k)))                                                 ≡⟨ fromParts′-prop (i , _) ⟩
        toℕ (fromParts′ (i , fromParts (j , k)))                                                ≡⟨ Parts.fromParts-fromPartsℕ (constParts a (b * c)) i _ ⟩
        Partsℕ.fromParts (constParts a (b * c)) (toℕ i , toℕ (fromParts (j , k)))           ≡⟨ ≡.cong₂ (λ x y → Partsℕ.fromParts (constParts a x) (toℕ i , y))
                                                                                                    (≡.sym (sum-replicate-* b c))
                                                                                                    (fromParts′-prop (j , k)) ⟩
        Partsℕ.fromParts (constParts a (sum (repl b c))) (toℕ i , toℕ (fromParts′ (j , k)))  ≡⟨ ≡.sym (Parts.fromParts-fromPartsℕ (constParts a _) i _) ⟩
        toℕ (Parts.fromParts (constParts a (sum (repl b c))) (i , fromParts′ (j , k)))        ≡⟨ Parts.fromParts-fromPartsℕ (constParts a (sum (repl b c))) i _ ⟩
        PNS.fromParts a (sum (repl b c)) (toℕ i , toℕ (fromParts′ (j , k)))                  ≡⟨ ≡.cong₂ (λ x y → PNS.fromParts a x (toℕ i , y))
                                                                                                    (sum-replicate-* b c)
                                                                                                    (Parts.fromParts-fromPartsℕ (constParts b c) j k) ⟩
        PNS.fromParts a (b * c) (toℕ i , PNS.fromParts b c (toℕ j , toℕ k))               ∎
      where
      open ≡.Reasoning

    fromParts³-prop : ∀ {a b c} (i : Fin a) (j : Fin b) (k : Fin c) → toℕ (fromParts³ (i , j , k)) ≡ PNS.fromParts³ a b c (toℕ i , toℕ j , toℕ k)
    fromParts³-prop {a} {b} {c} i j k =
      begin
        toℕ (fromParts (fromParts (i , j) , k))                                                  ≡⟨ fromParts′-prop (fromParts (i , j) , k) ⟩
        toℕ (fromParts′ (fromParts (i , j) , k))                                                 ≡⟨ Parts.fromParts-fromPartsℕ (constParts (a * b) c) (fromParts (i , j)) k ⟩
        Partsℕ.fromParts (constParts (a * b) c) (toℕ (fromParts (i , j)) , toℕ k)            ≡⟨ ≡.cong₂ (λ x y → Partsℕ.fromParts (constParts x c) (y , toℕ k))
                                                                                                     (≡.sym (sum-replicate-* a b))
                                                                                                     (fromParts′-prop (i , j)) ⟩
        Partsℕ.fromParts (constParts (sum (repl a b)) c) (toℕ (fromParts′ (i , j)) , toℕ k)   ≡⟨ ≡.sym (Parts.fromParts-fromPartsℕ (constParts _ c) (fromParts′ (i , j)) k) ⟩
        toℕ (fromParts′ (fromParts′ (i , j) , k))                                                 ≡⟨ Parts.fromParts-fromPartsℕ (constParts _ c) (fromParts′ (i , j)) k ⟩
        PNS.fromParts (sum (repl a b)) c (toℕ (fromParts′ (i , j)) , toℕ k)                   ≡⟨ ≡.cong₂ (λ x y → PNS.fromParts x c (y , toℕ k))
                                                                                                     (sum-replicate-* a b)
                                                                                                     (Parts.fromParts-fromPartsℕ (constParts a b) i j) ⟩
        PNS.fromParts (a * b) c (PNS.fromParts a b (toℕ i , toℕ j) , toℕ k)                ∎
      where open ≡.Reasoning

abstract
  fromParts-assoc : ∀ {a b c} (ijk : Fin a × Fin b × Fin c) → fromParts³ ijk ≅ fromParts³′ ijk
  fromParts-assoc {a} {b} {c} (i , j , k) =
    Fin.toℕ-injective′ (begin
      toℕ (fromParts³ (i , j , k))                       ≡⟨ fromParts³-prop i j k ⟩
      PNS.fromParts³ a b c (toℕ i , toℕ j , toℕ k)   ≡⟨ ≡.sym (PNS.fromParts-assoc _ _ _ (Fin.bounded i) (Fin.bounded j) (Fin.bounded k)) ⟩
      PNS.fromParts³′ a b c (toℕ i , toℕ j , toℕ k)  ≡⟨ ≡.sym (fromParts³′-prop i j k) ⟩
      toℕ (fromParts³′ (i , j , k))                      ∎)
    (Nat.*-assoc a _ _)
    where open ≡.Reasoning

module _ (a b c : ℕ) where

  toParts³ : Fin (a * b * c) → Fin a × Fin b × Fin c
  toParts³ x =
    let ij , k = toParts x
        i , j = toParts ij
    in i , j , k

  toParts³′ : Fin (a * (b * c)) → Fin a × Fin b × Fin c
  toParts³′ i =
    let i₁ , i₂₃ = toParts i
        i₂ , i₃ = toParts i₂₃
    in i₁ , i₂ , i₃

  abstract
    fromParts³-toParts³ : ∀ i → fromParts³ (toParts³ i) ≡ i
    fromParts³-toParts³ x =
      let i , j , k = toParts³ x
          open ≡.Reasoning
      in begin
        fromParts³ (toParts³ x)          ≡⟨⟩
        fromParts (fromParts (i , j) , k)  ≡⟨ ≡.cong (fromParts ∘ (_, k)) (asParts {a} {b} .Inverse.left-inverse-of (toParts x .proj₁)) ⟩
        fromParts {a * b} (toParts x)    ≡⟨ asParts {a * b} .Inverse.left-inverse-of x ⟩
        x                                  ∎

    toParts³′-fromParts³′ : ∀ ijk → toParts³′ (fromParts³′ ijk) ≡ ijk
    toParts³′-fromParts³′ (i , j , k) =
      let i′ , j′ , k′ = toParts³′ (fromParts³′ (i , j , k))
          p , q = Σ.≡⇒≡×≡ (asParts .Inverse.right-inverse-of (i , fromParts (j , k)))
          q′ = ≡.trans (≡.cong toParts q) (asParts .Inverse.right-inverse-of (j , k))

      in Σ.≡×≡⇒≡ (p , q′)

    toParts-assoc : {i : Fin (a * b * c)} {i′ : Fin (a * (b * c))} → i ≅ i′ → toParts³ i ≡ toParts³′ i′
    toParts-assoc {i} {i′} eq =
      begin
        toParts³ i                              ≡⟨ ≡.sym (toParts³′-fromParts³′ _) ⟩
        toParts³′ (fromParts³′ (toParts³ i))  ≡⟨ ≡.cong toParts³′ lem ⟩
        toParts³′ i′                            ∎
      where
      lem : fromParts³′ (toParts³ i) ≡ i′
      lem = ≅.≅-to-≡ (
        let open ≅.Reasoning
        in begin
          fromParts³′ (toParts³ i)   ≅⟨ ≅.sym (fromParts-assoc (toParts³ i)) ⟩
          fromParts³ (toParts³ i)    ≡⟨ fromParts³-toParts³ i ⟩
          i                            ≅⟨ eq ⟩
          i′                           ∎)

      open ≡.Reasoning

    toParts³-fromParts³ : ∀ ijk → toParts³ (fromParts³ ijk) ≡ ijk
    toParts³-fromParts³ ijk =
      begin
        toParts³  (fromParts³ ijk)    ≡⟨ toParts-assoc (fromParts-assoc ijk) ⟩
        toParts³′ (fromParts³′ ijk)   ≡⟨ toParts³′-fromParts³′ ijk ⟩
        ijk                             ∎
      where open ≡.Reasoning

    fromParts³′-toParts³′ : ∀ k → fromParts³′ (toParts³′ k) ≡ k
    fromParts³′-toParts³′ k =
      let k′ = ≡.subst Fin (≡.sym (Nat.*-assoc a b c)) k
          k′≅k = ≅.≡-subst-removable Fin _ k
      in ≅.≅-to-≡ (begin
        fromParts³′ (toParts³′ k )   ≡⟨ ≡.cong fromParts³′ (≡.sym (toParts-assoc k′≅k)) ⟩
        fromParts³′ (toParts³  k′)   ≅⟨ ≅.sym (fromParts-assoc (toParts³ k′)) ⟩
        fromParts³  (toParts³  k′)   ≡⟨ fromParts³-toParts³ k′ ⟩
        k′                             ≅⟨ k′≅k ⟩
        k                              ∎)
      where open ≅.Reasoning

  asParts³ : Fin (a * b * c) ↔ (Fin a × Fin b × Fin c)
  asParts³ = record
    { to = ≡.→-to-⟶ toParts³
    ; from = ≡.→-to-⟶ fromParts³
    ; inverse-of = record
      { left-inverse-of = fromParts³-toParts³
      ; right-inverse-of = toParts³-fromParts³
      }
    }

  asParts³′ : Fin (a * (b * c)) ↔ (Fin a × Fin b × Fin c)
  asParts³′ = record
    { to = ≡.→-to-⟶ toParts³′
    ; from = ≡.→-to-⟶ fromParts³′
    ; inverse-of = record
      { left-inverse-of = fromParts³′-toParts³′
      ; right-inverse-of = toParts³′-fromParts³′
      }
    }

abstract
  toParts-1ˡ : ∀ {b} (x : Fin (1 * b)) (x′ : Fin b) → x ≅ x′ → toParts {1} x ≡ (zero , x′)
  toParts-1ˡ {b} x x′ x≅x′ =
    let i  , j = toParts {1} x
        i′ , j′ = toParts′ {1} x
        i′′ , j′′ = Partsℕ.toParts (constParts 1 b) (toℕ x)
        i≅i′ , j≅j′ = Σ.≡⇒≡×≡ (toParts′-prop {1} {x = x} {x′ = x} ≅.refl)

        i′≅i′′ , j′≅j′′ = Σ.≡⇒≡×≡ (Parts.toParts-toPartsℕ (constParts 1 b) x)
        p , q = Σ.≡⇒≡×≡ (PNS.toParts-1ˡ {b} _ (Nat.≤-trans (Fin.bounded x) (Nat.≤-reflexive (Nat.*-identityˡ _))))
        open ≡.Reasoning
    in Σ.≡×≡⇒≡
      ( Fin.toℕ-injective (begin
          toℕ i  ≡⟨ i≅i′ ⟩
          toℕ i′ ≡⟨ i′≅i′′ ⟩
          i′′    ≡⟨ p ⟩
          0      ∎)
      , Fin.toℕ-injective (begin
          toℕ j    ≡⟨ j≅j′ ⟩
          toℕ j′   ≡⟨ j′≅j′′ ⟩
          j′′      ≡⟨ q ⟩
          toℕ x    ≡⟨ ≅.≅-to-≡ (≅.icong Fin (Nat.*-identityˡ _) toℕ x≅x′) ⟩
          toℕ x′   ∎)
      )

  toParts-1ʳ : ∀ {a} (x : Fin (a * 1)) (x′ : Fin a) → x ≅ x′ → toParts x ≡ (x′ , zero)
  toParts-1ʳ {a} x x′ x≅x′ =
    let x′′ : Fin (sum (repl a 1))
        x′′ = ≡.subst Fin (≡.sym (sum-replicate-* a 1)) x

        x≅x′′ = ≅.sym (≅.≡-subst-removable Fin (≡.sym (sum-replicate-* a 1)) x)
        x′′≅x′ = ≅.trans (≅.sym x≅x′′) x≅x′
        sra≡a = ≡.trans (sum-replicate-* a 1) (Nat.*-identityʳ a)

        i , j = toParts x
        i′ , j′ = toParts′ {a} {1} x′′
        i′′ , j′′ = Partsℕ.toParts (constParts a 1) (toℕ x′′)

        i≅i′ , j≅j′ = Σ.≡⇒≡×≡ (toParts′-prop {a} {x = x} {x′ = x′′} x≅x′′)
        i′≅i′′ , j′≅j′′ = Σ.≡⇒≡×≡ (Parts.toParts-toPartsℕ (constParts a 1) x′′)

        p , q = Σ.≡⇒≡×≡ (PNS.toParts-1ʳ {a} (toℕ x′′) (Nat.≤-trans (Nat.≤-reflexive (≅.≅-to-≡ (≅.icong Fin sra≡a (suc ∘ toℕ) x′′≅x′))) (Fin.bounded x′)))

        open ≡.Reasoning
    in Σ.≡×≡⇒≡
      ( Fin.toℕ-injective (begin
          toℕ i    ≡⟨ i≅i′ ⟩
          toℕ i′   ≡⟨ i′≅i′′ ⟩
          i′′      ≡⟨ p ⟩
          toℕ x′′  ≡⟨ ≅.≅-to-≡ (≅.icong Fin sra≡a toℕ x′′≅x′) ⟩
          toℕ x′   ∎)
      , Fin.toℕ-injective (begin
          toℕ j  ≡⟨ j≅j′ ⟩
          toℕ j′ ≡⟨ j′≅j′′ ⟩
          j′′     ≡⟨ q ⟩
          0      ∎)
      )
