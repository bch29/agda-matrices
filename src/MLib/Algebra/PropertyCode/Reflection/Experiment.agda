module MLib.Algebra.PropertyCode.Reflection.Experiment where

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
  ; getArg
  )

open import Reflection

inWeakenedContext : ∀ {a} {A : Set a} → ℕ → TC A → TC A
inWeakenedContext n action =
  getContext >>=′ λ ctx →
  inContext (List.drop n ctx) action

macro
  experiment : Term → TC ⊤
  experiment hole =
    getContext >>=′ λ ctx₁ →
    inWeakenedContext 1 getContext >>=′ λ ctx₂ →
    typeError (List.intersperse (strErr ",") (List.map (termErr ∘ getArg) (ctx₁ List.++ ctx₂)))

test : Fin 0 → Fin 1 → Fin 2 → ⊤
test i j k = experiment
