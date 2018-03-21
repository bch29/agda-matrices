
open import MLib.Prelude.FromStdlib

module MLib.Prelude.TransitiveProver {a p} {A : Set a} (_⇒_ : A → A → Set p) (trans : Transitive _⇒_) where

open List using ([]; _∷_)

open import Relation.Nullary using (yes; no)
open import Relation.Binary using (Decidable; IsStrictTotalOrder)

import Data.AVL as AVL

Database : Set (a ⊔ˡ p)
Database = List (∃₂ λ x y → x ⇒ y)

private
  data Chain (x y : A) : Set (a ⊔ˡ p) where
    inj :  (p : x ⇒ y) → Chain x y
    chain : ∀ {z} (ps : Chain x z) (qs : Chain z y) → Chain x y

  runChain : ∀ {x y} → Chain x y → x ⇒ y
  runChain (inj p) = p
  runChain (chain ps qs) = trans (runChain ps) (runChain qs)

module Search {r} {_<_ : Rel A r} (isStrictTotalOrder : IsStrictTotalOrder _≡_ _<_) where
  open IsStrictTotalOrder isStrictTotalOrder

  private
    module Tree = AVL isStrictTotalOrder
    open Tree using (Tree)

    Database′ = Tree (λ x → List (∃ λ y → x ⇒ y))

    mkDB : Database → Database′
    mkDB [] = Tree.empty
    mkDB ((x , y , p) ∷ ps) = Tree.insertWith x ((y , p) ∷ []) List._++_ (mkDB ps)

    record UnseenSet (n : ℕ) : Set (a ⊔ˡ p ⊔ˡ r) where
      constructor us
      field
        getUs : Tree (λ _ → ⊤)

    open UnseenSet

    emptyUnseen : UnseenSet 0
    emptyUnseen = us Tree.empty

    tryMarkUnseen : ∀ {n} → A → UnseenSet n → Maybe (UnseenSet (Nat.suc n))
    tryMarkUnseen x (us t) with Tree.lookup x t
    tryMarkUnseen x (us t) | just _ = nothing
    tryMarkUnseen x (us t) | nothing = just (us (Tree.insert x tt t))

    tryMarkSeen : ∀ {n} → A → UnseenSet (Nat.suc n) → Maybe (UnseenSet n)
    tryMarkSeen x (us t) with Tree.lookup x t
    tryMarkSeen x (us t) | just _ = just (us (Tree.delete x t))
    tryMarkSeen x (us t) | nothing = nothing

    initialUnseenSet : Database → ∃ UnseenSet
    initialUnseenSet [] = _ , emptyUnseen
    initialUnseenSet ((x , y , p) ∷ db) with initialUnseenSet db
    initialUnseenSet ((x , y , p) ∷ db) | _ , iu with tryMarkUnseen x iu
    initialUnseenSet ((x , y , p) ∷ db) | _ , iu | just r = _ , r
    initialUnseenSet ((x , y , p) ∷ db) | _ , iu | nothing = _ , iu

    _<|>_ : ∀ {a} {A : Set a} → Maybe A → Maybe A → Maybe A
    just x <|> _ = just x
    _ <|> y = y

    infixl 1 _>>=_

    _>>=_ : ∀ {a b} {A : Set a} {B : Set b} → Maybe A → (A → Maybe B) → Maybe B
    nothing >>= _ = nothing
    just x >>= f = f x

    firstMatching : ∀ {a b} {A : Set a} {B : Set b} → List A → (A → Maybe B) → Maybe B
    firstMatching [] f = nothing
    firstMatching (x ∷ xs) f = f x <|> firstMatching xs f

    getDec : ∀ {a} {A : Set a} → Dec A → Maybe A
    getDec (yes p) = just p
    getDec (no _) = nothing

    module _ (db : Database′) {t} where
      dfsFrom₁ : ∀ {n} {x} → UnseenSet (Nat.suc n) → Maybe (Chain x t)
      dfsFrom₂ : ∀ {n} {x} → UnseenSet n → ∀ {y} → x ⇒ y → Maybe (Chain x t)

      dfsFrom₁ {x = x} unseen =
        tryMarkSeen x unseen >>= λ unseen′ →
        Tree.lookup x db >>= λ ps →
        firstMatching ps λ {(y , p) → dfsFrom₂ unseen′ p}

      dfsFrom₂ unseen {y} p with y ≟ t
      dfsFrom₂ unseen {y} p | yes ≡.refl = just (inj p)
      dfsFrom₂ {Nat.zero} unseen {y} p | no _ = nothing
      dfsFrom₂ {Nat.suc n} unseen {y} p | no _ =
        Maybe.map (chain (inj p)) (dfsFrom₁ unseen)

    findChain : Database → ∀ x y → Maybe (Chain x y)
    findChain db x y with initialUnseenSet db
    ... | Nat.zero , unseen =
      -- The database is empty, so there can't be any chains
      nothing
    ... | Nat.suc n , unseen =
      let db′ = mkDB db
      in dfsFrom₁ db′ unseen

  tryProve : Database → ∀ x y → Maybe (x ⇒ y)
  tryProve db x y = findChain db x y >>= just ∘ runChain
