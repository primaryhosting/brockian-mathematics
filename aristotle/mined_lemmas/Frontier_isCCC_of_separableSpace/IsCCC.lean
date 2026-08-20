/-
# Suslin Line
Category: Frontier — Set Theory
Target: Frontier.Suslin_line
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` lines to precede any module docstring, so the header above is a
-- plain block comment and is repeated below as the module docstring.)

import Mathlib

/-!
# Suslin Line
Category: Frontier — Set Theory
Target: Frontier.Suslin_line
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace Frontier

open Set TopologicalSpace

universe u

/-- The **countable chain condition** (ccc) for a topological space `X`: every family of
pairwise disjoint nonempty open subsets of `X` is countable. -/

def IsCCC (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ A : Set (Set X), (∀ s ∈ A, IsOpen s) → (∀ s ∈ A, s.Nonempty) →
    A.PairwiseDisjoint id → A.Countable

/-- A **Suslin line**: a linearly ordered set, equipped with its order topology, which is
densely ordered without endpoints, satisfies the countable chain condition, but is *not*
separable (it has no countable dense subset).

This is the object whose existence Suslin's problem asks about: `ℝ` is characterised (up to
order isomorphism) as the unique complete densely ordered separable linear order without
endpoints, and Suslin asked whether "separable" can be weakened to "ccc". -/
structure IsSuslinLine (X : Type u) [LinearOrder X] [TopologicalSpace X] : Prop where
  /-- the topology is the order topology -/
  orderTopology : OrderTopology X
  /-- the order is dense -/
  denselyOrdered : DenselyOrdered X
  /-- there is no least element -/
  noMin : NoMinOrder X
  /-- there is no greatest element -/
  noMax : NoMaxOrder X
  /-- the countable chain condition holds -/
  ccc : IsCCC X
  /-- there is no countable dense subset -/
  not_separable : ¬ SeparableSpace X

/-- The statement "a Suslin line exists". -/
