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
  )

open import MLib.Algebra.PropertyCode.RawStruct
open import MLib.Algebra.PropertyCode.Core
import MLib.Prelude.DFS.ViaInjection as DFS

open import Function.Equivalence using (Equivalence)
open import Function.Equality using (_⟨$⟩_)
import Data.Bool.Properties as Bool
open Function using (case_of_)

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

  -- open Prover.Search {A = Properties code} _⇒ₚ_ ⇒ₚ-trans

  -- Prop = Property K × Term
  -- Props = Properties code × Term

  -- _∈ₜ_ : Prop → Props → Set
  -- (π , πt) ∈ₜ (Π , Πₜ) = π ∈ₚ Π

  -- _⇒ₜ_ : Props → Props → Set
  -- (Π₁ , Π₁t) ⇒ₜ (Π₂ , Π₂t) = Π₁ ⇒ₚ Π₂

  Impl = (∃₂ λ (Π₁ Π₂ : Properties code) → Π₁ ⇒ₚ Π₂)

  ImplSet = List (Impl × Term)

  argToImpl : ℕ → Arg Type → TC (Maybe (Impl × Term))
  argToImpl ix (arg _ (con (quote _⇒ₚ_) (_ ∷ _ ∷ arg (arg-info visible relevant) prop1 ∷ arg (arg-info visible relevant) prop2 ∷ []))) =
    catchTC
    (unquoteTC prop1 >>=′ λ (Π₁ : Properties code) →
     unquoteTC prop2 >>=′ λ (Π₂ : Properties code) →
     unquoteTC (var ix []) >>=′ λ (impl : Π₁ ⇒ₚ Π₂) →
     return (just ((Π₁ , Π₂ , impl) , var ix [])))
     -- If 'unquoteTC' fails at any point here it is because the implication is
     -- regarding properties on the wrong code, so return 'nothing'.
    (return nothing)
  argToImpl ix (arg _ _) = return nothing

  argToProperties : ℕ → Arg Type → TC (Maybe (Properties code × Term))
  argToProperties ix (arg _ propsTy) =
    catchTC
    (fmap (λ Π → just (Π , var ix [])) (unquoteTC propsTy))
    (return nothing)

  implsInScope : TC ImplSet
  implsInScope = getContext >>=′ itraverseMaybe argToImpl

  -- Given a set of property implications, find a particular property on the RHS of an impl.
  findProperty : ∀ π → ImplSet → List (∃₂ λ (Π₁ Π₂ : Properties code) → Π₁ ⇒ₚ Π₂ × π ∈ₚ Π₂)
  findProperty π = List.mapMaybe go
    where
    go : Impl × Term → Maybe (∃₂ λ Π₁ Π₂ → Π₁ ⇒ₚ Π₂ × π ∈ₚ Π₂)
    go ((Π₁ , Π₂ , p) , t) with hasProperty Π₂ π | ≡.inspect (hasProperty Π₂) π
    ... | false | _ = nothing
    ... | true | ≡.[ q ] = just (Π₁ , Π₂ , p , fromTruth (Equivalence.from Bool.T-≡ ⟨$⟩ q))

  -- implSetGraph : ImplSet → Search.Graph
  -- implSetGraph = ?
  --   where
  --   implSetDatabase : ImplSet → Database
  --   implSetDatabase = ?

  macro
    use : Property K → Term → TC ⊤
    use π goal =
      quoteTC π >>=′ λ π-term →
      implsInScope >>=′ λ Πs →
      case findProperty π Πs of λ
        { [] → typeError (strErr "can't find property" ∷ termErr π-term ∷ [])
        ; Πs@(_ ∷ _) → {!!}
        }
