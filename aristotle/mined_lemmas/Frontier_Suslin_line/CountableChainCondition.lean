import Mathlib
import RequestProject.CantorDedekind

/-!
# Suslin Line
Category: Frontier — Set Theory
Target: Frontier.Suslin_line
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open TopologicalSpace Set

namespace Frontier

/-- The **countable chain condition** (ccc) for a topological space `X`: every family of
pairwise disjoint nonempty open subsets of `X` is countable. -/

def CountableChainCondition (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ S : Set (Set X), (∀ s ∈ S, IsOpen s) → (∀ s ∈ S, s.Nonempty) →
    S.PairwiseDisjoint id → S.Countable

/-- A **Suslin line**: a densely ordered linear order without endpoints, equipped with its
order topology, which satisfies the countable chain condition but is *not* separable.

(Suslin's problem asks whether such a line exists; equivalently, whether every ccc dense
complete linear order without endpoints is order-isomorphic to `ℝ`.  The existence of a Suslin
line is independent of ZFC: Jensen's diamond principle `◊` implies one exists, while
`MA + ¬CH` implies none does.) -/
structure IsSuslinLine (X : Type u) [LinearOrder X] [TopologicalSpace X] : Prop where
  orderTopology : OrderTopology X
  denselyOrdered : DenselyOrdered X
  noMin : NoMinOrder X
  noMax : NoMaxOrder X
  ccc : CountableChainCondition X
  not_separable : ¬ SeparableSpace X

/-- **Suslin's Hypothesis** (SH): no Suslin line exists. -/
