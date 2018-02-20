module MLib.Algebra.Instances where

open import MLib.Prelude

it : ∀ {a} {A : Set a} → ⦃ x : A ⦄ → A
it ⦃ x ⦄ = x

data ⊤′ : Set where
  tt′ : ⊤′


test : ⊤′
test =
  let instance x = tt′
  in it

