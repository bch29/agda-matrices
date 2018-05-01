module MLib.Fin.Pieces.Simple where

open import MLib.Prelude
open import MLib.Fin.Pieces.Core
open import MLib.Fin.Pieces
open import MLib.Fin.Pieces.Nat
import MLib.Fin.Pieces.Nat.Simple as PNS

open Nat using (_*_; _+_; _<_)
open Fin using (toℕ; fromℕ≤)
open Table

open PNS using (sum-replicate-*; repl)

asPiece : ∀ {a b} → (Fin a × Fin b) ↔ Fin (a * b)
asPiece {a} {b} = ≡.subst (λ n → (Fin a × Fin b) ↔ Fin n) (sum-replicate-* a b) (Pieces.asPiece (constPieces a b))

intoPiece : ∀ {a b} → Fin a × Fin b → Fin (a * b)
intoPiece = Inverse.to asPiece ⟨$⟩_

fromPiece : ∀ {a b} → Fin (a * b) → Fin a × Fin b
fromPiece = Inverse.from asPiece ⟨$⟩_

intoPiece³′ : ∀ {a b c} → Fin a × Fin b × Fin c → Fin (a * (b * c))
intoPiece³′ {a} {b} {c} (i , j , k) = intoPiece (i , intoPiece (j , k))

intoPiece³ : ∀ {a b c} → Fin a × Fin b × Fin c → Fin (a * b * c)
intoPiece³ {a} {b} {c} (i , j , k) = intoPiece (intoPiece (i , j) , k)

private
  intoPiece′ : ∀ {a b} → Fin a × Fin b → Fin (sum (repl a b))
  intoPiece′ {a} {b} = Pieces.intoPiece (constPieces a b)

  fromPiece′ : ∀ {a b} → Fin (sum (repl a b)) → Fin a × Fin b
  fromPiece′ {a} {b} = Pieces.fromPiece (constPieces a b)

  asPiece-prop : ∀ {a b} → asPiece ≅ Pieces.asPiece (constPieces a b)
  asPiece-prop {a} {b} = ≅.≡-subst-removable _ _ _

  abstract
    intoPiece′-prop : ∀ {a b} (ij : Fin a × Fin b) → toℕ (intoPiece ij) ≡ toℕ (intoPiece′ ij)
    intoPiece′-prop {a} {b} ij =
      ≅.≅-to-≡ (≅.icong (λ n → (Fin a × Fin b) ↔ Fin n)
                         (≡.sym (sum-replicate-* a b))
                         (λ {n} (ap : (Fin a × Fin b) ↔ Fin n) → toℕ (Inverse.to ap ⟨$⟩ ij))
                         asPiece-prop)

    fromPiece′-prop : ∀ {a b} {x : Fin (a * b)} {x′ : Fin (sum (repl a b))} → x ≅ x′ → Σ.map toℕ toℕ (fromPiece {a} x) ≡ Σ.map toℕ toℕ (fromPiece′ {a} x′)
    fromPiece′-prop {a} {b} {x} {x′} x≅x′ =
      ≅.≅-to-≡ (≅.icong₂
        (λ n → (Fin a × Fin b) ↔ Fin n)
        (≡.sym (sum-replicate-* a b))
        (λ {n} (ap : (Fin a × Fin b) ↔ Fin n) x → Σ.map toℕ toℕ (Inverse.from ap ⟨$⟩ x))
        asPiece-prop
        x≅x′)

    intoPiece³′-prop : ∀ {a b c} (i : Fin a) (j : Fin b) (k : Fin c) → toℕ (intoPiece³′ (i , j , k)) ≡ PNS.intoPiece³′ a b c (toℕ i , toℕ j , toℕ k)
    intoPiece³′-prop {a} {b} {c} i j k =
      begin
        toℕ (intoPiece (i , intoPiece (j , k)))                                                 ≡⟨ intoPiece′-prop (i , _) ⟩
        toℕ (intoPiece′ (i , intoPiece (j , k)))                                                ≡⟨ Pieces.intoPiece-intoPieceℕ (constPieces a (b * c)) i _ ⟩
        Piecesℕ.intoPiece (constPieces a (b * c)) (toℕ i , toℕ (intoPiece (j , k)))           ≡⟨ ≡.cong₂ (λ x y → Piecesℕ.intoPiece (constPieces a x) (toℕ i , y))
                                                                                                    (≡.sym (sum-replicate-* b c))
                                                                                                    (intoPiece′-prop (j , k)) ⟩
        Piecesℕ.intoPiece (constPieces a (sum (repl b c))) (toℕ i , toℕ (intoPiece′ (j , k)))  ≡⟨ ≡.sym (Pieces.intoPiece-intoPieceℕ (constPieces a _) i _) ⟩
        toℕ (Pieces.intoPiece (constPieces a (sum (repl b c))) (i , intoPiece′ (j , k)))        ≡⟨ Pieces.intoPiece-intoPieceℕ (constPieces a (sum (repl b c))) i _ ⟩
        PNS.intoPiece a (sum (repl b c)) (toℕ i , toℕ (intoPiece′ (j , k)))                  ≡⟨ ≡.cong₂ (λ x y → PNS.intoPiece a x (toℕ i , y))
                                                                                                    (sum-replicate-* b c)
                                                                                                    (Pieces.intoPiece-intoPieceℕ (constPieces b c) j k) ⟩
        PNS.intoPiece a (b * c) (toℕ i , PNS.intoPiece b c (toℕ j , toℕ k))               ∎
      where
      open ≡.Reasoning

    intoPiece³-prop : ∀ {a b c} (i : Fin a) (j : Fin b) (k : Fin c) → toℕ (intoPiece³ (i , j , k)) ≡ PNS.intoPiece³ a b c (toℕ i , toℕ j , toℕ k)
    intoPiece³-prop {a} {b} {c} i j k =
      begin
        toℕ (intoPiece (intoPiece (i , j) , k))                                                  ≡⟨ intoPiece′-prop (intoPiece (i , j) , k) ⟩
        toℕ (intoPiece′ (intoPiece (i , j) , k))                                                 ≡⟨ Pieces.intoPiece-intoPieceℕ (constPieces (a * b) c) (intoPiece (i , j)) k ⟩
        Piecesℕ.intoPiece (constPieces (a * b) c) (toℕ (intoPiece (i , j)) , toℕ k)            ≡⟨ ≡.cong₂ (λ x y → Piecesℕ.intoPiece (constPieces x c) (y , toℕ k))
                                                                                                     (≡.sym (sum-replicate-* a b))
                                                                                                     (intoPiece′-prop (i , j)) ⟩
        Piecesℕ.intoPiece (constPieces (sum (repl a b)) c) (toℕ (intoPiece′ (i , j)) , toℕ k)   ≡⟨ ≡.sym (Pieces.intoPiece-intoPieceℕ (constPieces _ c) (intoPiece′ (i , j)) k) ⟩
        toℕ (intoPiece′ (intoPiece′ (i , j) , k))                                                 ≡⟨ Pieces.intoPiece-intoPieceℕ (constPieces _ c) (intoPiece′ (i , j)) k ⟩
        PNS.intoPiece (sum (repl a b)) c (toℕ (intoPiece′ (i , j)) , toℕ k)                   ≡⟨ ≡.cong₂ (λ x y → PNS.intoPiece x c (y , toℕ k))
                                                                                                     (sum-replicate-* a b)
                                                                                                     (Pieces.intoPiece-intoPieceℕ (constPieces a b) i j) ⟩
        PNS.intoPiece (a * b) c (PNS.intoPiece a b (toℕ i , toℕ j) , toℕ k)                ∎
      where open ≡.Reasoning

abstract
  intoPiece-assoc : ∀ {a b c} (ijk : Fin a × Fin b × Fin c) → intoPiece³ ijk ≅ intoPiece³′ ijk
  intoPiece-assoc {a} {b} {c} (i , j , k) =
    Fin.toℕ-injective′ (begin
      toℕ (intoPiece³ (i , j , k))                       ≡⟨ intoPiece³-prop i j k ⟩
      PNS.intoPiece³ a b c (toℕ i , toℕ j , toℕ k)   ≡⟨ ≡.sym (PNS.intoPiece-assoc _ _ _ (Fin.bounded i) (Fin.bounded j) (Fin.bounded k)) ⟩
      PNS.intoPiece³′ a b c (toℕ i , toℕ j , toℕ k)  ≡⟨ ≡.sym (intoPiece³′-prop i j k) ⟩
      toℕ (intoPiece³′ (i , j , k))                      ∎)
    (Nat.*-assoc a _ _)
    where open ≡.Reasoning

module _ (a b c : ℕ) where

  fromPiece³ : Fin (a * b * c) → Fin a × Fin b × Fin c
  fromPiece³ x =
    let ij , k = fromPiece x
        i , j = fromPiece ij
    in i , j , k

  fromPiece³′ : Fin (a * (b * c)) → Fin a × Fin b × Fin c
  fromPiece³′ i =
    let i₁ , i₂₃ = fromPiece i
        i₂ , i₃ = fromPiece i₂₃
    in i₁ , i₂ , i₃

  abstract
    intoPiece³-fromPiece³ : ∀ i → intoPiece³ (fromPiece³ i) ≡ i
    intoPiece³-fromPiece³ x =
      let i , j , k = fromPiece³ x
          open ≡.Reasoning
      in begin
        intoPiece³ (fromPiece³ x)          ≡⟨⟩
        intoPiece (intoPiece (i , j) , k)  ≡⟨ ≡.cong (intoPiece ∘ (_, k)) (asPiece {a} {b} .Inverse.right-inverse-of _) ⟩
        intoPiece {a * b} (fromPiece x)    ≡⟨ asPiece {a * b} .Inverse.right-inverse-of _ ⟩
        x                                  ∎

    fromPiece³′-intoPiece³′ : ∀ ijk → fromPiece³′ (intoPiece³′ ijk) ≡ ijk
    fromPiece³′-intoPiece³′ (i , j , k) =
      let i′ = proj₁ (fromPiece³′ (intoPiece³′ (i , j , k)))
          j′ = proj₁ (proj₂ (fromPiece³′ (intoPiece³′ (i , j , k))))
          k′ = proj₂ (proj₂ (fromPiece³′ (intoPiece³′ (i , j , k))))

          p , q = Σ.≡⇒≡×≡ (asPiece .Inverse.left-inverse-of _)
          q′ = ≡.trans (≡.cong fromPiece q) (asPiece .Inverse.left-inverse-of _)

      in Σ.≡×≡⇒≡ (p , q′)

    fromPiece-assoc : {i : Fin (a * b * c)} {i′ : Fin (a * (b * c))} → i ≅ i′ → fromPiece³ i ≡ fromPiece³′ i′
    fromPiece-assoc {i} {i′} eq =
      begin
        fromPiece³ i                              ≡⟨ ≡.sym (fromPiece³′-intoPiece³′ _) ⟩
        fromPiece³′ (intoPiece³′ (fromPiece³ i))  ≡⟨ ≡.cong fromPiece³′ lem ⟩
        fromPiece³′ i′                            ∎
      where
      lem : intoPiece³′ (fromPiece³ i) ≡ i′
      lem = ≅.≅-to-≡ (
        let open ≅.Reasoning
        in begin
          intoPiece³′ (fromPiece³ i)   ≅⟨ ≅.sym (intoPiece-assoc (fromPiece³ i)) ⟩
          intoPiece³ (fromPiece³ i)    ≡⟨ intoPiece³-fromPiece³ i ⟩
          i                            ≅⟨ eq ⟩
          i′                           ∎)

      open ≡.Reasoning

    fromPiece³-intoPiece³ : ∀ ijk → fromPiece³ (intoPiece³ ijk) ≡ ijk
    fromPiece³-intoPiece³ ijk =
      begin
        fromPiece³  (intoPiece³ ijk)    ≡⟨ fromPiece-assoc (intoPiece-assoc ijk) ⟩
        fromPiece³′ (intoPiece³′ ijk)   ≡⟨ fromPiece³′-intoPiece³′ ijk ⟩
        ijk                             ∎
      where open ≡.Reasoning

    intoPiece³′-fromPiece³′ : ∀ k → intoPiece³′ (fromPiece³′ k) ≡ k
    intoPiece³′-fromPiece³′ k =
      let k′ = ≡.subst Fin (≡.sym (Nat.*-assoc a b c)) k
          k′≅k = ≅.≡-subst-removable Fin _ k
      in ≅.≅-to-≡ (begin
        intoPiece³′ (fromPiece³′ k )   ≡⟨ ≡.cong intoPiece³′ (≡.sym (fromPiece-assoc k′≅k)) ⟩
        intoPiece³′ (fromPiece³  k′)   ≅⟨ ≅.sym (intoPiece-assoc (fromPiece³ k′)) ⟩
        intoPiece³  (fromPiece³  k′)   ≡⟨ intoPiece³-fromPiece³ k′ ⟩
        k′                             ≅⟨ k′≅k ⟩
        k                              ∎)
      where open ≅.Reasoning

  asPiece³ : (Fin a × Fin b × Fin c) ↔ Fin (a * b * c)
  asPiece³ = record
    { to = ≡.→-to-⟶ intoPiece³
    ; from = ≡.→-to-⟶ fromPiece³
    ; inverse-of = record
      { left-inverse-of = fromPiece³-intoPiece³
      ; right-inverse-of = intoPiece³-fromPiece³
      }
    }

  asPiece³′ : (Fin a × Fin b × Fin c) ↔ Fin (a * (b * c))
  asPiece³′ = record
    { to = ≡.→-to-⟶ intoPiece³′
    ; from = ≡.→-to-⟶ fromPiece³′
    ; inverse-of = record
      { left-inverse-of = fromPiece³′-intoPiece³′
      ; right-inverse-of = intoPiece³′-fromPiece³′
      }
    }

abstract
  fromPiece-1ˡ : ∀ {b} (x : Fin (1 * b)) (x′ : Fin b) → x ≅ x′ → fromPiece {1} x ≡ (zero , x′)
  fromPiece-1ˡ {b} x x′ x≅x′ =
    let i  , j = fromPiece {1} x
        i′ , j′ = fromPiece′ {1} x
        i′′ , j′′ = Piecesℕ.fromPiece (constPieces 1 b) (toℕ x)
        i≅i′ , j≅j′ = Σ.≡⇒≡×≡ (fromPiece′-prop {1} {x = x} {x′ = x} ≅.refl)

        i′≅i′′ , j′≅j′′ = Σ.≡⇒≡×≡ (Pieces.fromPiece-fromPieceℕ (constPieces 1 b) x)
        p , q = Σ.≡⇒≡×≡ (PNS.fromPiece-1ˡ {b} _ (Nat.≤-trans (Fin.bounded x) (Nat.≤-reflexive (Nat.*-identityˡ _))))
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

  fromPiece-1ʳ : ∀ {a} (x : Fin (a * 1)) (x′ : Fin a) → x ≅ x′ → fromPiece x ≡ (x′ , zero)
  fromPiece-1ʳ {a} x x′ x≅x′ =
    let x′′ : Fin (sum (repl a 1))
        x′′ = ≡.subst Fin (≡.sym (sum-replicate-* a 1)) x

        x≅x′′ = ≅.sym (≅.≡-subst-removable Fin (≡.sym (sum-replicate-* a 1)) x)
        x′′≅x′ = ≅.trans (≅.sym x≅x′′) x≅x′
        sra≡a = ≡.trans (sum-replicate-* a 1) (Nat.*-identityʳ a)

        i , j = fromPiece x
        i′ , j′ = fromPiece′ {a} {1} x′′
        i′′ , j′′ = Piecesℕ.fromPiece (constPieces a 1) (toℕ x′′)

        i≅i′ , j≅j′ = Σ.≡⇒≡×≡ (fromPiece′-prop {a} {x = x} {x′ = x′′} x≅x′′)
        i′≅i′′ , j′≅j′′ = Σ.≡⇒≡×≡ (Pieces.fromPiece-fromPieceℕ (constPieces a 1) x′′)

        p , q = Σ.≡⇒≡×≡ (PNS.fromPiece-1ʳ {a} (toℕ x′′) (Nat.≤-trans (Nat.≤-reflexive (≅.≅-to-≡ (≅.icong Fin sra≡a (suc ∘ toℕ) x′′≅x′))) (Fin.bounded x′)))

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
