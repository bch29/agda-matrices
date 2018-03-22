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

  _<|>_ : ∀ {a} {A : Set a} → Maybe A → Maybe A → Maybe A
  just x <|> _ = just x
  _ <|> y = y

  firstMatching : ∀ {a b} {A : Set a} {B : Set b} → List A → (A → Maybe B) → Maybe B
  firstMatching [] f = nothing
  firstMatching (x ∷ xs) f = f x <|> firstMatching xs f


module UseProperty {k} {code : Code k} {c ℓ} (rawStruct : RawStruct (Code.K code) c ℓ) {Π : Properties code} (reify : ∀ {π} → π ∈ₚ Π → ⟦ π ⟧P rawStruct) where
  open RawStruct rawStruct
  open Code code

  PropertiesSet = List (Properties code × Term)

  argToProperties : ℕ → Arg Type → TC (Maybe (Properties code × Term))
  argToProperties ix (arg _ propsTy) =
    catchTC
    (fmap (λ Π → just (Π , var ix [])) (unquoteTC propsTy))
    -- If 'unquoteTC' fails to produce a 'Properties code', this part of the
    -- context is not a set of properties so return 'nothing'
    (return nothing)

  propertiesInScope : TC PropertiesSet
  propertiesInScope = getContext >>=′ itraverseMaybe argToProperties

  findProperty : ∀ π → PropertiesSet → Maybe (Σ (Properties code) (λ Π → π ∈ₚ Π))
  findProperty π Πs = firstMatching Πs go
    where
    go : Properties code × Term → Maybe (Σ (Properties code) (λ Π → π ∈ₚ Π))
    go (Π , t) with hasProperty Π π | ≡.inspect (hasProperty Π) π
    go (Π , t) | false | _ = nothing
    go (Π , t) | true | ≡.[ p ] = just (Π , fromTruth (Equivalence.from Bool.T-≡ ⟨$⟩ p))

  macro
    use : Property K → Term → TC ⊤
    use π goal =
      propertiesInScope >>=′ λ Πs →
      case findProperty π Πs of λ
        { (just (Π , p)) →
          -- let res = 
        ; nothing → typeError (strErr "can't find desired property" ∷ [])
        }
