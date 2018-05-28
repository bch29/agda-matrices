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

asPart : ∀ {a b} → (Fin a × Fin b) ↔ Fin (a * b)
asPart {a} {b} = ≡.subst (λ n → (Fin a × Fin b) ↔ Fin n) (sum-replicate-* a b) (Parts.asPart (constParts a b))

intoPart : ∀ {a b} → Fin a × Fin b → Fin (a * b)
intoPart = Inverse.to asPart ⟨$⟩_

fromPart : ∀ {a b} → Fin (a * b) → Fin a × Fin b
fromPart = Inverse.from asPart ⟨$⟩_

intoPart³′ : ∀ {a b c} → Fin a × Fin b × Fin c → Fin (a * (b * c))
intoPart³′ {a} {b} {c} (i , j , k) = intoPart (i , intoPart (j , k))

intoPart³ : ∀ {a b c} → Fin a × Fin b × Fin c → Fin (a * b * c)
intoPart³ {a} {b} {c} (i , j , k) = intoPart (intoPart (i , j) , k)

private
  intoPart′ : ∀ {a b} → Fin a × Fin b → Fin (sum (repl a b))
  intoPart′ {a} {b} = Parts.intoPart (constParts a b)

  fromPart′ : ∀ {a b} → Fin (sum (repl a b)) → Fin a × Fin b
  fromPart′ {a} {b} = Parts.fromPart (constParts a b)

  asPart-prop : ∀ {a b} → asPart {a} {b} ≅ Parts.asPart (constParts a b)
  asPart-prop {a} {b} = ≅.≡-subst-removable _ _ _

  abstract
    intoPart′-prop : ∀ {a b} (ij : Fin a × Fin b) → toℕ (intoPart ij) ≡ toℕ (intoPart′ ij)
    intoPart′-prop {a} {b} ij =
      ≅.≅-to-≡ (≅.icong (λ n → (Fin a × Fin b) ↔ Fin n)
                         (≡.sym (sum-replicate-* a b))
                         (λ {n} (ap : (Fin a × Fin b) ↔ Fin n) → toℕ (Inverse.to ap ⟨$⟩ ij))
                         asPart-prop)

    fromPart′-prop : ∀ {a b} {x : Fin (a * b)} {x′ : Fin (sum (repl a b))} → x ≅ x′ → Σ.map toℕ toℕ (fromPart {a} x) ≡ Σ.map toℕ toℕ (fromPart′ {a} x′)
    fromPart′-prop {a} {b} {x} {x′} x≅x′ =
      ≅.≅-to-≡ (≅.icong₂
        (λ n → (Fin a × Fin b) ↔ Fin n)
        (≡.sym (sum-replicate-* a b))
        (λ {n} (ap : (Fin a × Fin b) ↔ Fin n) x → Σ.map toℕ toℕ (Inverse.from ap ⟨$⟩ x))
        asPart-prop
        x≅x′)

    intoPart³′-prop : ∀ {a b c} (i : Fin a) (j : Fin b) (k : Fin c) → toℕ (intoPart³′ (i , j , k)) ≡ PNS.intoPart³′ a b c (toℕ i , toℕ j , toℕ k)
    intoPart³′-prop {a} {b} {c} i j k =
      begin
        toℕ (intoPart (i , intoPart (j , k)))                                                 ≡⟨ intoPart′-prop (i , _) ⟩
        toℕ (intoPart′ (i , intoPart (j , k)))                                                ≡⟨ Parts.intoPart-intoPartℕ (constParts a (b * c)) i _ ⟩
        Partsℕ.intoPart (constParts a (b * c)) (toℕ i , toℕ (intoPart (j , k)))           ≡⟨ ≡.cong₂ (λ x y → Partsℕ.intoPart (constParts a x) (toℕ i , y))
                                                                                                    (≡.sym (sum-replicate-* b c))
                                                                                                    (intoPart′-prop (j , k)) ⟩
        Partsℕ.intoPart (constParts a (sum (repl b c))) (toℕ i , toℕ (intoPart′ (j , k)))  ≡⟨ ≡.sym (Parts.intoPart-intoPartℕ (constParts a _) i _) ⟩
        toℕ (Parts.intoPart (constParts a (sum (repl b c))) (i , intoPart′ (j , k)))        ≡⟨ Parts.intoPart-intoPartℕ (constParts a (sum (repl b c))) i _ ⟩
        PNS.intoPart a (sum (repl b c)) (toℕ i , toℕ (intoPart′ (j , k)))                  ≡⟨ ≡.cong₂ (λ x y → PNS.intoPart a x (toℕ i , y))
                                                                                                    (sum-replicate-* b c)
                                                                                                    (Parts.intoPart-intoPartℕ (constParts b c) j k) ⟩
        PNS.intoPart a (b * c) (toℕ i , PNS.intoPart b c (toℕ j , toℕ k))               ∎
      where
      open ≡.Reasoning

    intoPart³-prop : ∀ {a b c} (i : Fin a) (j : Fin b) (k : Fin c) → toℕ (intoPart³ (i , j , k)) ≡ PNS.intoPart³ a b c (toℕ i , toℕ j , toℕ k)
    intoPart³-prop {a} {b} {c} i j k =
      begin
        toℕ (intoPart (intoPart (i , j) , k))                                                  ≡⟨ intoPart′-prop (intoPart (i , j) , k) ⟩
        toℕ (intoPart′ (intoPart (i , j) , k))                                                 ≡⟨ Parts.intoPart-intoPartℕ (constParts (a * b) c) (intoPart (i , j)) k ⟩
        Partsℕ.intoPart (constParts (a * b) c) (toℕ (intoPart (i , j)) , toℕ k)            ≡⟨ ≡.cong₂ (λ x y → Partsℕ.intoPart (constParts x c) (y , toℕ k))
                                                                                                     (≡.sym (sum-replicate-* a b))
                                                                                                     (intoPart′-prop (i , j)) ⟩
        Partsℕ.intoPart (constParts (sum (repl a b)) c) (toℕ (intoPart′ (i , j)) , toℕ k)   ≡⟨ ≡.sym (Parts.intoPart-intoPartℕ (constParts _ c) (intoPart′ (i , j)) k) ⟩
        toℕ (intoPart′ (intoPart′ (i , j) , k))                                                 ≡⟨ Parts.intoPart-intoPartℕ (constParts _ c) (intoPart′ (i , j)) k ⟩
        PNS.intoPart (sum (repl a b)) c (toℕ (intoPart′ (i , j)) , toℕ k)                   ≡⟨ ≡.cong₂ (λ x y → PNS.intoPart x c (y , toℕ k))
                                                                                                     (sum-replicate-* a b)
                                                                                                     (Parts.intoPart-intoPartℕ (constParts a b) i j) ⟩
        PNS.intoPart (a * b) c (PNS.intoPart a b (toℕ i , toℕ j) , toℕ k)                ∎
      where open ≡.Reasoning

abstract
  intoPart-assoc : ∀ {a b c} (ijk : Fin a × Fin b × Fin c) → intoPart³ ijk ≅ intoPart³′ ijk
  intoPart-assoc {a} {b} {c} (i , j , k) =
    Fin.toℕ-injective′ (begin
      toℕ (intoPart³ (i , j , k))                       ≡⟨ intoPart³-prop i j k ⟩
      PNS.intoPart³ a b c (toℕ i , toℕ j , toℕ k)   ≡⟨ ≡.sym (PNS.intoPart-assoc _ _ _ (Fin.bounded i) (Fin.bounded j) (Fin.bounded k)) ⟩
      PNS.intoPart³′ a b c (toℕ i , toℕ j , toℕ k)  ≡⟨ ≡.sym (intoPart³′-prop i j k) ⟩
      toℕ (intoPart³′ (i , j , k))                      ∎)
    (Nat.*-assoc a _ _)
    where open ≡.Reasoning

module _ (a b c : ℕ) where

  fromPart³ : Fin (a * b * c) → Fin a × Fin b × Fin c
  fromPart³ x =
    let ij , k = fromPart x
        i , j = fromPart ij
    in i , j , k

  fromPart³′ : Fin (a * (b * c)) → Fin a × Fin b × Fin c
  fromPart³′ i =
    let i₁ , i₂₃ = fromPart i
        i₂ , i₃ = fromPart i₂₃
    in i₁ , i₂ , i₃

  abstract
    intoPart³-fromPart³ : ∀ i → intoPart³ (fromPart³ i) ≡ i
    intoPart³-fromPart³ x =
      let i , j , k = fromPart³ x
          open ≡.Reasoning
      in begin
        intoPart³ (fromPart³ x)          ≡⟨⟩
        intoPart (intoPart (i , j) , k)  ≡⟨ ≡.cong (intoPart ∘ (_, k)) (asPart {a} {b} .Inverse.right-inverse-of (fromPart x .proj₁)) ⟩
        intoPart {a * b} (fromPart x)    ≡⟨ asPart {a * b} .Inverse.right-inverse-of x ⟩
        x                                  ∎

    fromPart³′-intoPart³′ : ∀ ijk → fromPart³′ (intoPart³′ ijk) ≡ ijk
    fromPart³′-intoPart³′ (i , j , k) =
      let i′ , j′ , k′ = fromPart³′ (intoPart³′ (i , j , k))
          p , q = Σ.≡⇒≡×≡ (asPart .Inverse.left-inverse-of (i , intoPart (j , k)))
          q′ = ≡.trans (≡.cong fromPart q) (asPart .Inverse.left-inverse-of (j , k))

      in Σ.≡×≡⇒≡ (p , q′)

    fromPart-assoc : {i : Fin (a * b * c)} {i′ : Fin (a * (b * c))} → i ≅ i′ → fromPart³ i ≡ fromPart³′ i′
    fromPart-assoc {i} {i′} eq =
      begin
        fromPart³ i                              ≡⟨ ≡.sym (fromPart³′-intoPart³′ _) ⟩
        fromPart³′ (intoPart³′ (fromPart³ i))  ≡⟨ ≡.cong fromPart³′ lem ⟩
        fromPart³′ i′                            ∎
      where
      lem : intoPart³′ (fromPart³ i) ≡ i′
      lem = ≅.≅-to-≡ (
        let open ≅.Reasoning
        in begin
          intoPart³′ (fromPart³ i)   ≅⟨ ≅.sym (intoPart-assoc (fromPart³ i)) ⟩
          intoPart³ (fromPart³ i)    ≡⟨ intoPart³-fromPart³ i ⟩
          i                            ≅⟨ eq ⟩
          i′                           ∎)

      open ≡.Reasoning

    fromPart³-intoPart³ : ∀ ijk → fromPart³ (intoPart³ ijk) ≡ ijk
    fromPart³-intoPart³ ijk =
      begin
        fromPart³  (intoPart³ ijk)    ≡⟨ fromPart-assoc (intoPart-assoc ijk) ⟩
        fromPart³′ (intoPart³′ ijk)   ≡⟨ fromPart³′-intoPart³′ ijk ⟩
        ijk                             ∎
      where open ≡.Reasoning

    intoPart³′-fromPart³′ : ∀ k → intoPart³′ (fromPart³′ k) ≡ k
    intoPart³′-fromPart³′ k =
      let k′ = ≡.subst Fin (≡.sym (Nat.*-assoc a b c)) k
          k′≅k = ≅.≡-subst-removable Fin _ k
      in ≅.≅-to-≡ (begin
        intoPart³′ (fromPart³′ k )   ≡⟨ ≡.cong intoPart³′ (≡.sym (fromPart-assoc k′≅k)) ⟩
        intoPart³′ (fromPart³  k′)   ≅⟨ ≅.sym (intoPart-assoc (fromPart³ k′)) ⟩
        intoPart³  (fromPart³  k′)   ≡⟨ intoPart³-fromPart³ k′ ⟩
        k′                             ≅⟨ k′≅k ⟩
        k                              ∎)
      where open ≅.Reasoning

  asPart³ : (Fin a × Fin b × Fin c) ↔ Fin (a * b * c)
  asPart³ = record
    { to = ≡.→-to-⟶ intoPart³
    ; from = ≡.→-to-⟶ fromPart³
    ; inverse-of = record
      { left-inverse-of = fromPart³-intoPart³
      ; right-inverse-of = intoPart³-fromPart³
      }
    }

  asPart³′ : (Fin a × Fin b × Fin c) ↔ Fin (a * (b * c))
  asPart³′ = record
    { to = ≡.→-to-⟶ intoPart³′
    ; from = ≡.→-to-⟶ fromPart³′
    ; inverse-of = record
      { left-inverse-of = fromPart³′-intoPart³′
      ; right-inverse-of = intoPart³′-fromPart³′
      }
    }

abstract
  fromPart-1ˡ : ∀ {b} (x : Fin (1 * b)) (x′ : Fin b) → x ≅ x′ → fromPart {1} x ≡ (zero , x′)
  fromPart-1ˡ {b} x x′ x≅x′ =
    let i  , j = fromPart {1} x
        i′ , j′ = fromPart′ {1} x
        i′′ , j′′ = Partsℕ.fromPart (constParts 1 b) (toℕ x)
        i≅i′ , j≅j′ = Σ.≡⇒≡×≡ (fromPart′-prop {1} {x = x} {x′ = x} ≅.refl)

        i′≅i′′ , j′≅j′′ = Σ.≡⇒≡×≡ (Parts.fromPart-fromPartℕ (constParts 1 b) x)
        p , q = Σ.≡⇒≡×≡ (PNS.fromPart-1ˡ {b} _ (Nat.≤-trans (Fin.bounded x) (Nat.≤-reflexive (Nat.*-identityˡ _))))
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

  fromPart-1ʳ : ∀ {a} (x : Fin (a * 1)) (x′ : Fin a) → x ≅ x′ → fromPart x ≡ (x′ , zero)
  fromPart-1ʳ {a} x x′ x≅x′ =
    let x′′ : Fin (sum (repl a 1))
        x′′ = ≡.subst Fin (≡.sym (sum-replicate-* a 1)) x

        x≅x′′ = ≅.sym (≅.≡-subst-removable Fin (≡.sym (sum-replicate-* a 1)) x)
        x′′≅x′ = ≅.trans (≅.sym x≅x′′) x≅x′
        sra≡a = ≡.trans (sum-replicate-* a 1) (Nat.*-identityʳ a)

        i , j = fromPart x
        i′ , j′ = fromPart′ {a} {1} x′′
        i′′ , j′′ = Partsℕ.fromPart (constParts a 1) (toℕ x′′)

        i≅i′ , j≅j′ = Σ.≡⇒≡×≡ (fromPart′-prop {a} {x = x} {x′ = x′′} x≅x′′)
        i′≅i′′ , j′≅j′′ = Σ.≡⇒≡×≡ (Parts.fromPart-fromPartℕ (constParts a 1) x′′)

        p , q = Σ.≡⇒≡×≡ (PNS.fromPart-1ʳ {a} (toℕ x′′) (Nat.≤-trans (Nat.≤-reflexive (≅.≅-to-≡ (≅.icong Fin sra≡a (suc ∘ toℕ) x′′≅x′))) (Fin.bounded x′)))

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
