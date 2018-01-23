
--------------------------------------------------------------------------------
-- Author : Bradley Hardy
--------------------------------------------------------------------------------
-- The first exercise from the ACS Algebraic Path Problems course, taught by
-- Timothy Griffin
--
-- Final proofs of 'fun fun facts' are at the bottom of the file; the rest
-- consists of definitions and supplementary proofs.
--------------------------------------------------------------------------------

module MLib.Lattices {ℓ} {S : Set ℓ} where

open import Matrix.Prelude

open import Function using (flip)

open Algebra.FunctionProperties (_≡_ {A = S}) using (Associative; Idempotent; Commutative)

module OperatorProperties (_∙_ : S → S → S) where
  _≤L_ = λ a b → a ≡ a ∙ b
  _≤R_ = λ a b → b ≡ a ∙ b

-- open OperatorProperties using (Associative; Idempotent; Commutative)

--------------------------------------------------------------------------------
--  Semigroups
--------------------------------------------------------------------------------

record IsCISemigroup (_∙_ : S → S → S) : Set ℓ where
  field
    isAssociative : Associative _∙_
    isIdempotent : Idempotent _∙_
    isCommutative : Commutative _∙_

  open OperatorProperties _∙_ public

  ≤L→flip≤R : ∀ {x y} → x ≤L y → y ≤R x
  ≤L→flip≤R p = ≡.trans p (isCommutative _ _)

  ≤R→flip≤L : ∀ {x y} → x ≤R y → y ≤L x
  ≤R→flip≤L p = ≡.trans p (isCommutative _ _)

  ≤L-isPartialOrder : IsPartialOrder _≡_ _≤L_
  ≤L-isPartialOrder =
    record
    { isPreorder =
      record
      { isEquivalence = ≡.isEquivalence
      ; reflexive = λ {i j} p →
        begin
          i           ≡⟨ ≡.sym (isIdempotent _) ⟩
          i ∙ i       ≡⟨ ≡.cong₂ _∙_ ≡.refl p ⟩
          i ∙ j       ∎
      ; trans = λ {i j k} p q →
        begin
          i             ≡⟨ p ⟩
          i ∙ j         ≡⟨ ≡.cong₂ _∙_ ≡.refl q ⟩
          i ∙ (j ∙ k)   ≡⟨ ≡.sym (isAssociative _ _ _) ⟩
          (i ∙ j) ∙ k   ≡⟨ ≡.cong₂ _∙_ (≡.sym p) ≡.refl ⟩
          i ∙ k         ∎
      }
    ; antisym = λ {x y} p q →
      begin
         x        ≡⟨ p ⟩
         x ∙ y    ≡⟨ isCommutative _ _ ⟩
         y ∙ x    ≡⟨ ≡.sym q ⟩
         y        ∎
    }
    where open ≡.≡-Reasoning

  -- Prove this by deferring to ≤L-isPartialOrder and taking advantage of the
  -- fact that _≤L_ and _≤R_ are dual.
  ≤R-isPartialOrder : IsPartialOrder _≡_ _≤R_
  ≤R-isPartialOrder =
    record
    { isPreorder =
      record
      { isEquivalence = ≡.isEquivalence
      ; reflexive = λ p → fromL (≤L.reflexive (≡.sym p))
      ; trans = λ {i j k} p q → fromL (≤L.trans (toL q) (toL p))
      }
    ; antisym = λ {x y} p q → ≤L.antisym (toL q) (toL p)
    }
    where module ≤L = IsPartialOrder ≤L-isPartialOrder
          fromL = ≤L→flip≤R
          toL = ≤R→flip≤L

--------------------------------------------------------------------------------
--  (Greatest) lower and (least) upper bounds
--------------------------------------------------------------------------------

record IsLowerBound (_≤_ : S → S → Set ℓ) (c a b : S) : Set ℓ where
  field
    ≤L : c ≤ a
    ≤R : c ≤ b

record IsGlb (_≤_ : S → S → Set ℓ) (c a b : S) : Set ℓ where
  field
    isLowerBound : IsLowerBound _≤_ c a b
    isGreatest : ∀ {d} → d ≤ a → d ≤ b → d ≤ c

  open IsLowerBound isLowerBound public

record IsUpperBound (_≤_ : S → S → Set ℓ) (c a b : S) : Set ℓ where
  field
    L≤ : a ≤ c
    R≤ : b ≤ c

record IsLub (_≤_ : S → S → Set ℓ) (c a b : S) : Set ℓ where
  field
    isUpperBound : IsUpperBound _≤_ c a b
    isLeast : ∀ {d} → a ≤ d → b ≤ d → c ≤ d

  open IsUpperBound isUpperBound public

  -- A least upper bound is a greatest lower bound with respect to the reversed
  -- order.
  flipGlb : IsGlb (flip _≤_) c a b
  flipGlb = record
    { isLowerBound = record { ≤L = L≤ ; ≤R = R≤ }
    ; isGreatest = isLeast
    }

module IsGlbProperties {≤ c a b} (isGlb : IsGlb ≤ c a b) where
  open IsGlb isGlb public

  sym : IsGlb ≤ c b a
  sym = record
    { isLowerBound = record { ≤L = ≤R ; ≤R = ≤L }
    ; isGreatest = λ x y → isGreatest y x
    }

  -- A greatest lower bound is a least upper bound with respect to the reversed
  -- order.
  flipLub : IsLub (flip ≤) c a b
  flipLub = record
    { isUpperBound = record { L≤ = ≤L ; R≤ = ≤R }
    ; isLeast = isGreatest
    }

module PartialOrderProperties (_≤_ : S → S → Set ℓ)
                              (isPartialOrder : IsPartialOrder _≡_ _≤_)
                              where
  module ≤ = IsPartialOrder isPartialOrder

  IsGlb-self : ∀ {a} → IsGlb _≤_ a a a
  IsGlb-self = record
    { isLowerBound = record { ≤L = ≤.refl ; ≤R = ≤.refl }
    ; isGreatest = λ x y → x
    }

  -- In a partial order, there is at most one greatest lower bound for any given
  -- pair of values.
  IsGlb-unique : ∀ {a b c} → IsGlb _≤_ c a b → ∀ {d} → IsGlb _≤_ d a b → c ≡ d
  IsGlb-unique p q =
    ≤.antisym
    (IsGlb.isGreatest q (IsGlb.≤L p) (IsGlb.≤R p))
    (IsGlb.isGreatest p (IsGlb.≤L q) (IsGlb.≤R q))

  flipIsPartialOrder : IsPartialOrder _≡_ (flip _≤_)
  flipIsPartialOrder = record
    { isPreorder = record
      { isEquivalence = ≡.isEquivalence
      ; reflexive = λ p → ≤.reflexive (≡.sym p)
      ; trans = flip ≤.trans
      }
      ; antisym = flip ≤.antisym
    }

--------------------------------------------------------------------------------
--  Semilattices
--------------------------------------------------------------------------------

record IsMeetSemilattice (_≤_ : S → S → Set ℓ) (_⊓_ : S → S → S) : Set ℓ where
  field
    isPartialOrder : IsPartialOrder _≡_ _≤_
    isGlb : ∀ {a b} → IsGlb _≤_ (a ⊓ b) a b

  open PartialOrderProperties _≤_ isPartialOrder public
  module This {a b} = IsGlbProperties (isGlb {a} {b})
  open This public

  -- In a meet semilattice, the only greatest lower bound of any pair 'a' and
  -- 'b' is 'a ⊓ b'.
  glb-intro : ∀ {c a b} → IsGlb _≤_ c a b → c ≡ a ⊓ b
  glb-intro p = IsGlb-unique p isGlb

  module CISemigroup where
    isCommutative : Commutative _⊓_
    isCommutative _ _ = glb-intro (IsGlbProperties.sym isGlb)

    isIdempotent : Idempotent _⊓_
    isIdempotent _ = ≡.sym (glb-intro IsGlb-self)

    isAssociative : Associative _⊓_
    isAssociative a b c =
      let d = (a ⊓ b) ⊓ c

          d≤a : d ≤ a
          d≤a = ≤.trans ≤L ≤L

          d≤b : d ≤ b
          d≤b = ≤.trans ≤L ≤R

          d≤c : d ≤ c
          d≤c = ≤R

          d≤b⊓c : d ≤ (b ⊓ c)
          d≤b⊓c = isGreatest d≤b d≤c

          d-greatest : ∀ {d′} → d′ ≤ a → d′ ≤ b → d′ ≤ c → d′ ≤ d
          d-greatest p q r = isGreatest (isGreatest p q) r
      in glb-intro (
         record
         { isLowerBound = record { ≤L = ≤.trans ≤L ≤L ; ≤R = d≤b⊓c}
         ; isGreatest = λ p q → d-greatest p (≤.trans q ≤L) (≤.trans q ≤R)
         })

  -- A meet semilattic is also a commutative idempotent semigroup
  isCISemigroup : IsCISemigroup _⊓_
  isCISemigroup = record { CISemigroup }

record IsJoinSemilattice (≤ : S → S → Set ℓ) (_⊔_ : S → S → S) : Set ℓ where
  field
    isPartialOrder : IsPartialOrder _≡_ ≤
    isLub : ∀ {a b} → IsLub ≤ (a ⊔ b) a b

  open PartialOrderProperties ≤ isPartialOrder public
  module This {a b} = IsLub (isLub {a} {b})
  open This

  -- A join semilattice is a meet semilattice with respect to the reversed order
  flipIsMeetSemilattice : IsMeetSemilattice (flip ≤) _⊔_
  flipIsMeetSemilattice = record
    { isPartialOrder = flipIsPartialOrder
    ; isGlb = flipGlb
    }

  -- A join semilattice is also a commutative idempotent semigroup
  open IsMeetSemilattice flipIsMeetSemilattice using (isCISemigroup) public

module MeetSemilatticeProperties {≤ ⊓}
                                 (isMeetSemilattice : IsMeetSemilattice ≤ ⊓)
                                 where

  open IsMeetSemilattice isMeetSemilattice

  -- A meet semilattice is a join semilattice with respect to the reversed order
  flipIsJoinSemilattice : IsJoinSemilattice (flip ≤) ⊓
  flipIsJoinSemilattice = record
    { isPartialOrder = flipIsPartialOrder
    ; isLub = flipLub
    }

--------------------------------------------------------------------------------
--  Proofs of fun fun facts
--------------------------------------------------------------------------------

-- Commutative idempotent semigroups create meet and join semilattices from
-- their left and right natural orders respectively.
module FunFunFact1 {_∙_ : S → S → S} (isCISemigroup : IsCISemigroup _∙_) where
  open IsCISemigroup isCISemigroup

  funFunFact1Meet : IsMeetSemilattice _≤L_ _∙_
  funFunFact1Meet =
    record
    { isPartialOrder = ≤L-isPartialOrder
    ; isGlb = λ {a b} → record
      { isLowerBound = record
        { ≤L =
          begin
            a ∙ b          ≡⟨ ≡.cong₂ _∙_ (≡.sym (isIdempotent _)) ≡.refl ⟩
            (a ∙ a) ∙ b    ≡⟨ isAssociative _ _ _ ⟩
            a ∙ (a ∙ b)    ≡⟨ isCommutative _ _ ⟩
            (a ∙ b) ∙ a    ∎
        ; ≤R =
          begin
            a ∙ b         ≡⟨ ≡.cong₂ _∙_ ≡.refl (≡.sym (isIdempotent _)) ⟩
            a ∙ (b ∙ b)   ≡⟨ ≡.sym (isAssociative _ _ _) ⟩
            (a ∙ b) ∙ b   ∎
        }
      ; isGreatest = λ {d} p q →
        begin
          d                 ≡⟨ ≡.sym (isIdempotent _) ⟩
          d ∙ d             ≡⟨ ≡.cong₂ _∙_ p q ⟩
          (d ∙ a) ∙ (d ∙ b) ≡⟨ isAssociative _ _ _ ⟩
          d ∙ (a ∙ (d ∙ b)) ≡⟨ ≡.cong₂ _∙_ ≡.refl (≡.sym (isAssociative _ _ _)) ⟩
          d ∙ ((a ∙ d) ∙ b) ≡⟨ ≡.cong₂ _∙_ ≡.refl
                               (≡.cong₂ _∙_ (isCommutative _ _) ≡.refl) ⟩
          d ∙ ((d ∙ a) ∙ b) ≡⟨ ≡.cong₂ _∙_ ≡.refl (isAssociative _ _ _) ⟩
          d ∙ (d ∙ (a ∙ b)) ≡⟨ ≡.sym (isAssociative _ _ _) ⟩
          (d ∙ d) ∙ (a ∙ b) ≡⟨ ≡.cong₂ _∙_ (isIdempotent _) ≡.refl ⟩
          d ∙ (a ∙ b)       ∎
      }
    }
    where open ≡.≡-Reasoning

  -- Prove for join by symmetry with meet
  funFunFact1Join : IsJoinSemilattice _≤R_ _∙_
  funFunFact1Join =
    record
    { isPartialOrder = ≤R-isPartialOrder
    ; isLub = λ {a b} → record
      { isUpperBound = record
        { L≤ = fromL Meet.≤L
        ; R≤ = fromL Meet.≤R
        }
      ; isLeast =
        λ {d} p q →
        fromL (Meet.isGreatest (toL p) (toL q))
      }
    }
    where
      open ≡.≡-Reasoning
      module Meet = IsMeetSemilattice funFunFact1Meet
      toL = ≤R→flip≤L
      fromL = ≤L→flip≤R

-- Semilattices are commutative idempotent semigroups
module FunFunFact2 {≤ : S → S → Set ℓ} where
  funFunFact2Meet : ∀ {⊓} → IsMeetSemilattice ≤ ⊓ → IsCISemigroup ⊓
  funFunFact2Meet ijs = isCISemigroup
    where open IsMeetSemilattice ijs

  -- Note this is using 'isCISemigroup' from the flipped /meet/ semilattice.
  funFunFact2Join : ∀ {⊔} → IsJoinSemilattice ≤ ⊔ → IsCISemigroup ⊔
  funFunFact2Join ijs = isCISemigroup
    where open IsJoinSemilattice ijs
