module MLib.Fin.Parts.Nat.Simple.Properties where

open import MLib.Prelude
open import MLib.Fin.Parts.Nat
import MLib.Fin.Parts.Nat.Simple as S

module P a b = Partsℕ (S.repl a b)

open Nat using (_*_; _+_; _<_)
open Fin using (toℕ; fromℕ≤)
open List


fromAny : ∀ a b → Any Fin (S.repl a b) → ℕ × ℕ
fromAny zero b ()
fromAny (suc a) b (here j) = 0 , Fin.toℕ j
fromAny (suc a) b (there js) =
  let i , j = fromAny a b js
  in suc i , j

intoPart-prop : ∀ a b {ps : Any Fin (S.repl a b)} → P.intoPart a b ps ≡ S.intoPart a b (fromAny a b ps)
intoPart-prop zero b {()}
intoPart-prop (suc a) b {here px} = ≡.sym (Nat.+-identityʳ _)
intoPart-prop (suc a) b {there ps} =
  let ind = intoPart-prop a b {ps}
      i , j = fromAny a b ps
      open ≡.Reasoning
      open Nat.SemiringSolver
  in begin
    b + Impl.intoPart ps ≡⟨ ≡.cong₂ _+_ ≡.refl ind ⟩
    b + (j + i * b)         ≡⟨ solve 3 (λ b j ib → b :+ (j :+ ib) := j :+ (b :+ ib)) ≡.refl b j (i * b) ⟩
    j + (b + i * b)       ∎

lem : ∀ a b {k} → k < a * b → k < sum (S.repl a b)
lem a b p = Nat.≤-trans p (Nat.≤-reflexive (≡.sym (S.sum-replicate-* a b)))

fromPart-prop : ∀ a b {k} → k < a * b → Maybe.map (fromAny a b) (Impl.fromPart (S.repl a b) k) ≡ just (S.fromPart a b k)
fromPart-prop zero b ()
fromPart-prop (suc a) b {k} p with Impl.compare′ k b
fromPart-prop (suc a) .(suc (m + k)) {.m} p | Impl.less m k = ≡.cong just (Σ.≡×≡⇒≡ (≡.refl , Fin.toℕ-fromℕ≤ _))
fromPart-prop (suc a) b {.(b + k)} p | Impl.gte .b k with Impl.fromPart (S.repl a b) k | fromPart-prop a b {k} (Nat.+-cancelˡ-< b p)
fromPart-prop (suc a) b {.(b + k)} p | Impl.gte .b k | just x | ind =
  let e1 , e2 = Σ.≡⇒≡×≡ (Maybe.just-injective ind)
  in ≡.cong just (Σ.≡×≡⇒≡ (≡.cong suc e1 , e2))
fromPart-prop (suc a) b {.(b + k)} p | Impl.gte .b k | nothing | ()

fromPart′-prop : ∀ a b {k} (p : k < a * b) → fromAny a b (P.fromPart a b {k} (lem a b p)) ≡ S.fromPart a b k
fromPart′-prop a b {k} p with Impl.fromPart (S.repl a b) k | Impl.fromPart-prop (S.repl a b) (lem a b p) | fromPart-prop a b p
fromPart′-prop a b {k} p | just x | y | z = Maybe.just-injective z
fromPart′-prop a b {k} p | nothing | () | z
