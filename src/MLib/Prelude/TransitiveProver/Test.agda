module MLib.Prelude.TransitiveProver.Test where

open import MLib.Prelude.FromStdlib

open import Data.Nat
open import Data.Nat.Properties

open import MLib.Prelude.TransitiveProver _≤_ ≤-trans

open Search <-isStrictTotalOrder


p1 : 1 ≤ 3
p1 = s≤s z≤n

p2 : 3 ≤ 5
p2 = s≤s (s≤s (s≤s z≤n))

p3 : 5 ≤ 9
p3 = s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))

p4 : 3 ≤ 6
p4 = s≤s (s≤s (s≤s z≤n))

p5 : 9 ≤ 13
p5 = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))

p6 : 5 ≤ 13
p6 = s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))

p7 : 3 ≤ 3
p7 = s≤s (s≤s (s≤s z≤n))


db : Database
db
  = (_ , _ , p4)
  ∷ (_ , _ , p7)
  -- ∷ (_ , _ , p3)
  ∷ (_ , _ , p1)
  ∷ (_ , _ , p5)
  ∷ (_ , _ , p2)
  ∷ (_ , _ , p6)
  ∷ (_ , _ , p3)
  ∷ []

res : 3 ≤ 9
res = s≤s (s≤s (s≤s z≤n))

-- test1 : tryProve db 3 9 ≡ just res
-- test1 = ≡.refl

test2 = findTransTargets db 1
