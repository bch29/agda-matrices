open import MLib.Prelude.FromStdlib
open import Relation.Binary using (Decidable; IsStrictTotalOrder)

module MLib.Prelude.DFS
  {v p e} {V : Set v} (_⇒_ : V → V → Set e)
  {_<_ : V → V → Set p} (isStrictTotalOrder : IsStrictTotalOrder _≡_ _<_)
  where

import Data.AVL isStrictTotalOrder as Tree
open Tree using (Tree)


-- A (directed) graph is a map from vertices to the list of edges out of that
-- vertex.
Graph = Tree (λ x → List (∃ λ y → x ⇒ y))


data Path (x y : V) : Set (v ⊔ˡ e) where
  edge :  (edge : x ⇒ y) → Path x y
  connect : ∀ {z} (p₁ : Path x z) (p₂ : Path z y) → Path x y


module Unseen where
  -- Represents a set of vertices have yet to be seen. Contains /at most/ 'n'
  -- vertices.
  record UnseenSet (n : ℕ) : Set (v ⊔ˡ e ⊔ˡ p) where
    constructor mkUnseen
    field
      getUnseen : Tree (λ _ → ⊤)

  empty : UnseenSet 0
  empty = mkUnseen Tree.empty

  -- mark a vertex as seen
  unmark : ∀ {n} → V → UnseenSet n → Maybe (UnseenSet (Nat.suc n))
  unmark x (mkUnseen t) with Tree.lookup x t
  unmark x (mkUnseen t) | just _ = nothing
  unmark x (mkUnseen t) | nothing = just (mkUnseen (Tree.insert x tt t))

  -- mark a vertex as unseen
  mark : ∀ {n} → V → UnseenSet (Nat.suc n) → Maybe (UnseenSet n)
  mark x (mkUnseen t) with Tree.lookup x t
  mark x (mkUnseen t) | just _ = just (mkUnseen (Tree.delete x t))
  mark x (mkUnseen t) | nothing = nothing

  isUnseen : ∀ {n} → V → UnseenSet n → Bool
  isUnseen x (mkUnseen t) =
    case Tree.lookup x t of λ
    { (just _) → true
    ; nothing → false
    }

  -- make an unseen set from all the vertices in the given graph which are the
  -- source of any edge
  allSources : Graph → ∃ UnseenSet
  allSources = go ∘ Tree.toList
    where
    step : Σ V (λ x → List (∃ (_⇒_ x))) → ∃ UnseenSet → ∃ UnseenSet
    step (x , _) (n , u) =
      case unmark x u of λ
      { (just u′) → _ , u′
      ; nothing → _ , u
      }

    go : List (Σ V (λ x → List (∃ (_⇒_ x)))) → ∃ UnseenSet
    go = List.foldr step (0 , empty)

  inj : ∀ {m n} → m Nat.≤ n → UnseenSet m → UnseenSet n
  inj _ (mkUnseen t) = mkUnseen t

open Unseen using (UnseenSet)

module _ (graph : Graph) where

  private
    go₁ : ∀ {n} (source : V) → UnseenSet n → ∃ (λ n′ → n′ Nat.≤ n × UnseenSet n′) × List (∃ (Path source))
    go₂ : ∀ {n} (source : V) → UnseenSet (Nat.suc n) → ∃ (λ n′ → n′ Nat.≤ Nat.suc n × UnseenSet n′) × List (∃ (Path source))
    go₃ : ∀ {n} (source : V) → List (∃ (λ dest → source ⇒ dest)) → UnseenSet n → ∃ (λ n′ → n′ Nat.≤ n × UnseenSet n′) × List (∃ (Path source))

    -- If there are no vertices left to visit, stop
    go₁ {Nat.zero} source unseen = (_ , Nat.z≤n , unseen) , []
    --
    go₁ {Nat.suc n} source unseen = go₂ source unseen

    go₂ {n} source unseen =
      case Unseen.mark source unseen of λ
        -- this source vertex has not been visited; recurse
        { (just unseen′) →
          case Tree.lookup source graph of λ
          -- We have a list of edges from this source to some other vertex. For
          -- each of these, a recursive call will only return paths from that
          -- vertex if it is yet unseen.
          { (just es) →
            let (n′ , n′≤n , unseen′′) , ps = go₃ source es unseen′
            in (n′ , Nat.≤-trans n′≤n (Nat.n≤1+n _) , unseen′′) ,
               (List.map (λ {(_ , e) → _ , edge e}) es List.++ ps)
          -- there are no edges from this source so nothing is reachable from it
          ; nothing → (_ , Nat.n≤1+n _ , unseen′) , []
          }
        -- this source vertex has already been visited; do nothing
        ; nothing → (_ , Nat.≤-refl , unseen) , []
        }

    go₃ source [] unseen = (_ , Nat.≤-refl , unseen) , []
    go₃ {n} source ((d , e) ∷ es) unseen =
      case go₁ d unseen of λ
      { ((n′ , n′≤n , unseen′) , paths-from-d) →
        case go₃ source es (Unseen.inj {n = n} n′≤n unseen′) of λ
        { (unseen′′ , restPaths) →
          let paths-via-d = List.map (λ {(d′ , p) → _ , connect (edge e) p}) paths-from-d
              -- Only add the path corresponding to the edge 'e' if 'd' has not
              -- been previously visited.
              paths-of-e = if Unseen.isUnseen d unseen′ then (_ , edge e) ∷ [] else []
          in unseen′′ , paths-of-e List.++ paths-via-d List.++ restPaths
        }
      }

  -- Given a source vertex S, finds all vertices T such that there is a path
  -- from S to T, and returns the path. No target vertex is returned more than
  -- once.
  allTargetsFrom : (source : V) → List (∃ (Path source))
  allTargetsFrom source =
    let _ , unseen = Unseen.allSources graph
    in proj₂ (go₁ source unseen)
