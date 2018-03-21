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


module UseProperty {k} {code : Code k} {c ℓ} (rawStruct : RawStruct (Code.K code) c ℓ) where
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

  findProperty : Property K → PropertiesSet → Maybe Term
  findProperty π Πs = {!!}
