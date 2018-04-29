module MLib.Prelude.TransitiveProver.Test where

open import MLib.Prelude.FromStdlib

open import Data.Nat
open import Data.Nat.Properties

open import MLib.Prelude.TransitiveProver _≤_ ≤-trans

open Search <-isStrictTotalOrder


1≤3 : 1 ≤ 3
1≤3 = s≤s z≤n

3≤5 : 3 ≤ 5
3≤5 = s≤s (s≤s (s≤s z≤n))

5≤9 : 5 ≤ 9
5≤9 = s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))

3≤6 : 3 ≤ 6
3≤6 = s≤s (s≤s (s≤s z≤n))

9≤13 : 9 ≤ 13
9≤13 = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))

5≤13 : 5 ≤ 13
5≤13 = s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))

3≤3 : 3 ≤ 3
3≤3 = s≤s (s≤s (s≤s z≤n))


db : Database
db
  = (_ , _ , 1≤3)
  ∷ (_ , _ , 3≤3)
  ∷ (_ , _ , 3≤6)
  ∷ (_ , _ , 9≤13)
  ∷ (_ , _ , 3≤5)
  ∷ (_ , _ , 3≤5)
  ∷ (_ , _ , 5≤13)
  ∷ (_ , _ , 5≤9)
  ∷ []

res : 3 ≤ 9
res = s≤s (s≤s (s≤s z≤n))

test1 : tryProve db 3 9 ≡ just res
test1 = ≡.refl

test2 = findTransTargets db 1
