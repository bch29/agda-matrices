module MLib.Algebra.PropertyCode.Reflection where

open import MLib.Prelude
open import Holes.Prelude
  using
  ( RawMonad
  ; _>>=_
  ; return
  ; _>>=′_
  ; fmap
  ; _<$>_
  ; _>>=²_
  ; TC-Monad
  ; Maybe-Monad
  ; mapArg
  ; mapAbs
  )

open import MLib.Algebra.PropertyCode.RawStruct
open import MLib.Algebra.PropertyCode.Core
open import MLib.Prelude.Path
import MLib.Prelude.DFS.ViaInjection as DFS

open import Function.Equivalence using (Equivalence)
open import Function.Equality using (_⟨$⟩_)
import Data.Bool.Properties as Bool
open Function using (case_of_)
open import Relation.Binary using (_Respects₂_)

open import Reflection

private
  imap : ∀ {a b} {A : Set a} {B : Set b} → (ℕ → A → B) → List A → List B
  imap f [] = []
  imap f (x ∷ xs) = f 0 x ∷ imap (f ∘ Nat.suc) xs

  imapMaybe : ∀ {a b} {A : Set a} {B : Set b} → (ℕ → A → Maybe B) → List A → List B
  imapMaybe f [] = []
  imapMaybe f (x ∷ xs) with f 0 x
  ... | just x′ = x′ ∷ imapMaybe (f ∘ Nat.suc) xs
  ... | nothing = imapMaybe (f ∘ Nat.suc) xs

  itraverseMaybe : ∀ {a b} {A : Set a} {B : Set b} → (ℕ → A → TC (Maybe B)) → List A → TC (List B)
  itraverseMaybe f [] = return []
  itraverseMaybe f (x ∷ xs) =
    let mxs′ = itraverseMaybe (f ∘ Nat.suc) xs
    in f 0 x >>=′ λ
       { (just x′) → fmap (λ xs′ → x′ ∷ xs′) mxs′
       ; nothing → mxs′
       }

  firstMatching : ∀ {a b} {A : Set a} {B : Set b} → List A → (A → Maybe B) → Maybe B
  firstMatching [] f = nothing
  firstMatching (x ∷ xs) f = f x <|> firstMatching xs f


module UseProperty {k} {code : Code k} {c ℓ} (rawStruct : RawStruct (Code.K code) c ℓ) {Π : Properties code} (reify : ∀ {π} → π ∈ₚ Π → ⟦ π ⟧P rawStruct) where
  open RawStruct rawStruct
  open Code code

  module Props = Setoid (Properties-setoid {code = code})
  open Props using () renaming (_≈_ to _≈ₚ_)

  private
    ⇒ₚ-reflexive : ∀ {Π Π′ : Properties code} → Π ≈ₚ Π′ → Π ⇒ₚ Π′
    ⇒ₚ-reflexive {Π} {Π′} p = →ₚ-⇒ₚ go
      where
      go : ∀ π → π ∈ₚ Π → π ∈ₚ Π′
      go π (fromTruth truth) = fromTruth (≡.subst Bool.T (p Property.refl) truth)

  ⇒ₚ-subst : _⇒ₚ_ Respects₂ _≈ₚ_
  proj₁ ⇒ₚ-subst {Γ} {Π} {Π′} e p = ⇒ₚ-trans p (⇒ₚ-reflexive e)
  proj₂ ⇒ₚ-subst {Γ} {Π} {Π′} e p = ⇒ₚ-trans (⇒ₚ-reflexive (Props.sym e)) p

  open DFS (Properties-setoid {code = code}) (Function.flip _⇒ₚ_) (proj₂ ⇒ₚ-subst , proj₁ ⇒ₚ-subst) Nat.<-isStrictTotalOrder Properties↞ℕ

  -- Prop = Property K × Term
  -- Props = Properties code × Term

  -- _∈ₜ_ : Prop → Props → Set
  -- (π , πt) ∈ₜ (Π , Πₜ) = π ∈ₚ Π

  -- _⇒ₜ_ : Props → Props → Set
  -- (Π₁ , Π₁t) ⇒ₜ (Π₂ , Π₂t) = Π₁ ⇒ₚ Π₂

  Impl = (∃₂ λ (Π₁ Π₂ : Properties code) → Π₂ ⇒ₚ Π₁)

  ImplSet = List (Impl × Term)

  -- inWeakenedContext : ∀ {a} {A : Set a} → ℕ → TC A → TC A
  -- inWeakenedContext n action =
  --   getContext >>=′ λ ctx →
  --   inContext (List.drop n ctx) action

  -- TODO: make this respect lambdas
  {-# TERMINATING #-}
  mapVars : (ℕ → ℕ) → Term → Term
  mapVars f (var x args) = var (f x) (List.map (mapArg (mapVars f)) args)
  mapVars f (con c args) = con c (List.map (mapArg (mapVars f)) args)
  mapVars f (def n args) = def n (List.map (mapArg (mapVars f)) args)
  mapVars f (lam v t) = lam v (mapAbs (mapVars f) t)
  mapVars f (pat-lam cs args) = pat-lam cs (List.map (mapArg (mapVars f)) args)
  mapVars f (pi a b) = pi (mapArg (mapVars f) a) (mapAbs (mapVars f) b)
  mapVars f (sort (set t)) = sort (set (mapVars f t))
  mapVars f (sort (lit n)) = sort (lit n)
  mapVars f (sort unknown) = sort unknown
  mapVars f (lit l) = lit l
  mapVars f (meta x args) = meta x (List.map (mapArg (mapVars f)) args)
  mapVars f unknown = unknown

  argToImpl : ℕ → Type → TC (Maybe (Impl × Term))
  argToImpl ix (def (quote _⇒ₚ_) (_ ∷ _ ∷ arg (arg-info visible relevant) prop1 ∷ arg (arg-info visible relevant) prop2 ∷ [])) =
    catchTC
    (unquoteTC prop1 >>=′ λ (Π₂ : Properties code) →
     unquoteTC prop2 >>=′ λ (Π₁ : Properties code) →
     unquoteTC (var ix []) >>=′ λ (impl : Π₂ ⇒ₚ Π₁) →
     return (just ((Π₁ , Π₂ , impl) , var ix [])))
     -- If 'unquoteTC' fails at any point here it is because the implication is
     -- regarding properties on the wrong code, so return 'nothing'.
    (return nothing)
  argToImpl ix _ = return nothing

  argToImpl′ : ℕ → Arg Type → TC (Maybe (Impl × Term))
  argToImpl′ ix (arg _ t) =
    getContext >>=′ λ ctx →
    normalise (mapVars (λ v → (v Nat.+ ix Nat.+ 1)) t) >>=′ argToImpl ix

  implsInScope : TC ImplSet
  implsInScope = getContext >>=′ itraverseMaybe argToImpl′
    -- typeError ∘ List.map (termErr ∘ Holes.Prelude.getArg)

  implSetGraph : ImplSet → Graph
  implSetGraph = mkGraph ∘ List.map proj₁

  macro
    use : Property K → Term → TC ⊤
    use π goal =
      quoteTC π >>=′ λ π-term →
      implsInScope >>=′ λ Πs →
      -- quoteTC (List.length Πs) >>=′ λ len →
      -- typeError (strErr "got impls, length" ∷ termErr len ∷ [])
      let gr = implSetGraph Πs
          res = findMatching gr (λ Π′ → hasProperty Π′ π) Π
      in quoteTC res >>=′ λ t → typeError (strErr "test" ∷ termErr t ∷ [])
      -- in case findMatching gr (λ Π′ → hasProperty Π′ π) Π of λ
      --    { (just (Π′ , path , hasπ)) →
      --      let impl : Π′ ⇒ₚ Π
      --          impl = transPath (Function.flip ⇒ₚ-trans) path
      --          mem : π ∈ₚ Π′
      --          mem = fromTruth hasπ
      --          res = ⇒ₚ-MP mem impl
      --      in
      --      typeError (strErr "found solution" ∷ [])
      --         -- quoteTC res >>=′ λ t →
      --         -- typeError (strErr "found solution" ∷ termErr t ∷ [])
      --        -- unify goal
      --    ; nothing → typeError (strErr "no solution" ∷ [])
      --      -- quoteTC Πs >>=′ λ Πs-term →
      --      -- typeError (strErr "can't find property" ∷ termErr π-term ∷ strErr "in graph" ∷ termErr Πs-term ∷ [])
      --    }
