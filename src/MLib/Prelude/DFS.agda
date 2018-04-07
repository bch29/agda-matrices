open import MLib.Prelude.FromStdlib
open import Relation.Binary using (Decidable; IsStrictTotalOrder)

module MLib.Prelude.DFS
  {v p e} {V : Set v} (_⇒_ : V → V → Set e)
  {_<_ : V → V → Set p} (isStrictTotalOrder : IsStrictTotalOrder _≡_ _<_)
  where

open import MLib.Prelude.Path
open Bool using (T)
open import Function.Equivalence using (Equivalence)
open import Function.Equality using (_⟨$⟩_)

import Data.AVL isStrictTotalOrder as Tree
open Tree using (Tree)


-- A (directed) graph is a map from vertices to the list of edges out of that
-- vertex.
Graph = Tree (λ x → List (∃ λ y → x ⇒ y))


private
  module Seen where
    -- Represents a set of vertices that have been seen. At most 'n' vertices
    -- have /not/ been seen.
    record SeenSet (n : ℕ) : Set (v ⊔ˡ e ⊔ˡ p) where
      constructor mkSeen
      field
        getSeen : Tree (λ _ → ⊤)

    isSeen : ∀ {n} → V → SeenSet n → Bool
    isSeen x (mkSeen t) = x Tree.∈? t

    -- Mark a vertex as seen, thus reducing the number of /unseen/ vertices.
    mark : ∀ {n} → V → SeenSet (Nat.suc n) → Maybe (SeenSet n)
    mark x u@(mkSeen t) = if Bool.not (isSeen x u) then just (mkSeen (Tree.insert x tt t)) else nothing

    -- Make a seen set for a particular graph. The number of unseen vertices in
    -- the result is bounded above by the number of vertices in the graph.
    forGraph : Graph → ∃ SeenSet
    forGraph gr = (countVertices gr , mkSeen Tree.empty)
      where
      -- this overcounts but that doesn't matter because the index is only there
      -- to ensure termination of the DFS
      countVertices : Graph → ℕ
      countVertices = List.foldr (λ { (_ , es) n → List.foldr (λ _ → Nat.suc) n es }) 0 ∘ Tree.toList

    inj : ∀ {n} → SeenSet n → SeenSet (Nat.suc n)
    inj (mkSeen t) = mkSeen t

open Seen using (SeenSet)

private
  infixl 1 _>>=ₛ_

  MonadDfs : ∀ {a} → ℕ → Set a → Set (v ⊔ˡ (p ⊔ˡ (e ⊔ˡ a)))
  MonadDfs n A = SeenSet n → A × SeenSet n

  runMonadDfs : ∀ {n a} {A : Set a} → MonadDfs n A → SeenSet n → A
  runMonadDfs f = proj₁ ∘ f

  _>>=ₛ_ : ∀ {n a b} {A : Set a} {B : Set b} → MonadDfs n A → (A → MonadDfs n B) → MonadDfs n B
  (f >>=ₛ g) s =
    let x , s′ = f s
    in g x s′

  returnₛ : ∀ {n a} {A : Set a} → A → MonadDfs n A
  returnₛ x s = x , s

  withMarked : ∀ {n a} {A : Set a} V → MonadDfs n A → MonadDfs (Nat.suc n) (Maybe A)
  withMarked v f s =
    case Seen.mark v s of λ
    { (just s′) →
      let x , s′′ = f s′
      in just x , Seen.inj s′′
    ; nothing → nothing , s
    }


module _ (graph : Graph) where

  private
    PathsFrom = List ∘ ∃ ∘ Path _⇒_

    -- Calculates paths from the given source to every reachable target not in
    -- the seen set. Returns the new seen set, the list of paths found, and
    -- a boolean indicating whether this source was previously in the seen
    -- set.
    pathsFromSource : ∀ {n} (source : V) → MonadDfs n (Maybe (PathsFrom source))

    -- Calculates paths from the given source to every reachable target not in
    -- the seen set, whose first edge is among the list given.
    pathsViaEdges : ∀ {n} {source : V} → List (∃ (λ dest → source ⇒ dest)) → MonadDfs n (PathsFrom source)

    -- Calculates paths via the edge given to every reachable target not in the
    -- seen set.
    pathsViaEdge : ∀ {n} {source dest : V} → source ⇒ dest → MonadDfs n (PathsFrom source)

    -- The base case of induction on the size of the seen set. This is only here
    -- to satisfy the termination checker.
    pathsFromSource {Nat.zero} source = returnₛ nothing
    pathsFromSource {Nat.suc _} source = withMarked source (
      case Tree.lookup source graph of λ
      -- We have a list of edges from this source to some other vertex. For
      -- each of these, a recursive call will only return paths from that
      -- vertex if it is yet unseen. Note the recursive call is on a seen set
      -- with an index one lower, satisfying Agda's termination checker.
      { (just es) → pathsViaEdges es >>=ₛ returnₛ ∘ just
      -- there are no edges from this source so nothing is reachable from it
      ; nothing → returnₛ (just [])
      }) >>=ₛ maybe returnₛ (returnₛ nothing)

    pathsViaEdges [] = returnₛ []
    pathsViaEdges ((d , e) ∷ es) =
      pathsViaEdge e >>=ₛ λ pathsVia-d →
      pathsViaEdges es >>=ₛ λ restPaths →
      returnₛ (pathsVia-d List.++ restPaths)

    pathsViaEdge {dest = d} e =
      pathsFromSource d >>=ₛ λ
      { (just pathsFrom-d) →
        let pathsVia-d = List.map (λ {(d′ , p) → d′ , connect (edge e) p}) pathsFrom-d
        in returnₛ ((_ , edge e) ∷ pathsVia-d)
      ; nothing → returnₛ []
      }

  -- Given a source vertex S, finds all vertices T such that there is a path
  -- from S to T, and returns the path. No target vertex is returned more than
  -- once.
  allTargetsFrom : (source : V) → List (∃ (Path _⇒_ source))
  allTargetsFrom source =
    let _ , seen = Seen.forGraph graph
    in maybe id [] (runMonadDfs (pathsFromSource source) seen)


module _ (graph : Graph) (matches : V → Bool) where

  private
    findMatchingFrom : ∀ {n} (source : V) → MonadDfs n (Maybe (∃ λ dest → Path _⇒_ source dest × T (matches dest)))
    findMatchingViaEdges : ∀ {n} {source : V} → List (∃ (λ inter → source ⇒ inter)) → MonadDfs n (Maybe (∃ λ dest → Path _⇒_ source dest × T (matches dest)))
    findMatchingViaEdge : ∀ {n} {source inter : V} → source ⇒ inter → MonadDfs n (Maybe (∃ λ dest → Path _⇒_ source dest × T (matches dest)))

    -- The base case of induction on the size of the seen set. This is only here
    -- to satisfy the termination checker.
    findMatchingFrom {Nat.zero} source = returnₛ nothing
    findMatchingFrom {Nat.suc _} source = withMarked source (
      case Tree.lookup source graph of λ
      -- We have a list of edges from this source to some other vertex. For
      -- each of these, a recursive call will only return paths from that
      -- vertex if it is yet unseen. Note the recursive call is on a seen set
      -- with an index one lower, satisfying Agda's termination checker.
      { (just es) → findMatchingViaEdges es
      -- there are no edges from this source so nothing is reachable from it
      ; nothing → returnₛ nothing
      }) >>=ₛ maybe returnₛ (returnₛ nothing)

    findMatchingViaEdges [] = returnₛ nothing
    findMatchingViaEdges ((d , e) ∷ es) =
      findMatchingViaEdge e >>=ₛ λ
      { (just r) → returnₛ (just r)
      ; nothing → findMatchingViaEdges es
      }

    findMatchingViaEdge {inter = d} e with matches d | ≡.inspect matches d
    findMatchingViaEdge {inter = _} e | true | ≡.[ eq ] = returnₛ (just (_ , edge e , Equivalence.from Bool.T-≡ ⟨$⟩ eq))
    findMatchingViaEdge {inter = d} e | false | _ =
      findMatchingFrom d >>=ₛ λ
      { (just (_ , p , q)) → returnₛ (just (_ , connect (edge e) p , q))
      ; nothing → returnₛ nothing
      }

  -- Given a source vertex S, finds all vertices T such that there is a path
  -- from S to T, and returns the path. No target vertex is returned more than
  -- once.
  findMatching : (source : V) → Maybe (∃ λ dest → Path _⇒_ source dest × T (matches dest))
  findMatching source =
    let _ , seen = Seen.forGraph graph
    in runMonadDfs (findMatchingFrom source) seen

module _ (graph : Graph) {dest} (isDest : ∀ v → Dec (v ≡ dest)) where
  -- Given a source vertex S, finds all vertices T such that there is a path
  -- from S to T, and returns the path. No target vertex is returned more than
  -- once.
  findDest : (source : V) → Maybe (Path _⇒_ source dest)
  findDest source with findMatching graph (⌊_⌋ ∘ isDest) source
  ... | just (dest′ , p , q) with isDest dest′
  ... | yes ≡.refl = just p
  findDest source | just (_ , _ , ()) | no _
  findDest source | nothing = nothing
