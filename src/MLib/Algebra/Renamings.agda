module MLib.Algebra.Renamings where

open import Algebra

import Algebra.Operations.CommutativeMonoid as CMO

module Semigroup′ {c ℓ} (semigroup : Semigroup c ℓ) where
  open Semigroup semigroup

  module Additive where
    infixl 6 _+_
    _+_ = _∙_
    module + = Semigroup semigroup renaming (∙-cong to cong)

  module Multiplicative where
    open Semigroup semigroup public
      using ()
      renaming (_∙_ to _*_)
    module * = Additive.+

  module Additive′ = Additive renaming (_+_ to _+′_; module + to +′)
  module Additive₁ = Additive renaming (_+_ to _+₁_; module + to +₁)
  module Additive₂ = Additive renaming (_+_ to _+₂_; module + to +₂)
  module Additive₃ = Additive renaming (_+_ to _+₃_; module + to +₃)
  module Additive₄ = Additive renaming (_+_ to _+₄_; module + to +₄)
  module Additive● = Additive renaming (_+_ to _⊕_; module + to ⊕)
  module Additive■ = Additive renaming (_+_ to _⊞_; module + to ⊞)

  module Multiplicative′ = Multiplicative renaming (_*_ to _*′_; module * to *′)
  module Multiplicative₁ = Multiplicative renaming (_*_ to _*₁_; module * to *₁)
  module Multiplicative₂ = Multiplicative renaming (_*_ to _*₂_; module * to *₂)
  module Multiplicative₃ = Multiplicative renaming (_*_ to _*₃_; module * to *₃)
  module Multiplicative₄ = Multiplicative renaming (_*_ to _*₄_; module * to *₄)
  module Multiplicative● = Multiplicative renaming (_*_ to _⊛_; module * to ⊛)


module Monoid′ {c ℓ} (monoid : Monoid c ℓ) where
  open Monoid monoid

  module Additive where
    open Semigroup′.Additive semigroup public using (_+_)
    module + where
      open Monoid monoid public
        renaming (∙-cong to cong)

    open Monoid monoid public
      using () renaming (ε to 0#)

  module Multiplicative where
    open Semigroup′.Multiplicative semigroup public using (_*_)
    module * = Additive.+

    open Monoid monoid public
      using () renaming (ε to 1#)

  module Additive′ = Additive renaming (_+_ to _+′_; 0# to 0′; module + to +′)
  module Additive₁ = Additive renaming (_+_ to _+₁_; 0# to 0₁; module + to +₁)
  module Additive₂ = Additive renaming (_+_ to _+₂_; 0# to 0₂; module + to +₂)
  module Additive₃ = Additive renaming (_+_ to _+₃_; 0# to 0₃; module + to +₃)
  module Additive₄ = Additive renaming (_+_ to _+₄_; 0# to 0₄; module + to +₄)
  module Additive● = Additive renaming (_+_ to _⊕_; 0# to 0●; module + to ⊕)
  module Additive■ = Additive renaming (_+_ to _⊞_; 0# to 0■; module + to ⊞)

  module Multiplicative′ = Multiplicative renaming (_*_ to _*′_; 1# to 1′; module * to *′)
  module Multiplicative₁ = Multiplicative renaming (_*_ to _*₁_; 1# to 1₁; module * to *₁)
  module Multiplicative₂ = Multiplicative renaming (_*_ to _*₂_; 1# to 1₂; module * to *₂)
  module Multiplicative₃ = Multiplicative renaming (_*_ to _*₃_; 1# to 1₃; module * to *₃)
  module Multiplicative₄ = Multiplicative renaming (_*_ to _*₄_; 1# to 1₄; module * to *₄)
  module Multiplicative● = Multiplicative renaming (_*_ to _⊛_; 1# to 1●; module * to ⊛)

module CommutativeMonoid′ {c ℓ} (commutativeMonoid : CommutativeMonoid c ℓ) where
  open CommutativeMonoid commutativeMonoid

  module Additive where
    open Monoid′.Additive public using (_+_)
    module + where
      open CommutativeMonoid commutativeMonoid public
        renaming (∙-cong to cong)

  module Multiplicative where
    open Monoid′.Multiplicative public using (_*_)
    module * = Additive.+

module Semiring′ {c ℓ} (semiring : Semiring c ℓ) where
  open Semiring semiring
  private
    module + = CommutativeMonoid′ +-commutativeMonoid
    module * = Monoid′ *-monoid

  module As′ where
    open +.Additive′ public
    open *.Multiplicative′ public
  module As₁ where
    open +.Additive₁ public
    open *.Multiplicative₁ public
  module As₂ where
    open +.Additive₂ public
    open *.Multiplicative₂ public
  module As₃ where
    open +.Additive₃ public
    open *.Multiplicative₃ public
  module As₄ where
    open +.Additive₄ public
    open *.Multiplicative₄ public
  module As● where
    open +.Additive● public
    open *.Multiplicative● public
