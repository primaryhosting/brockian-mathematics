import Mathlib

/-!
# Suslin Line
Category: Frontier — Set Theory
Target: Frontier.Suslin_line
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Classical

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace Frontier

open Set TopologicalSpace

universe u

/-- The **countable chain condition** (ccc): every family of pairwise disjoint nonempty open
sets is countable. -/

theorem suslinHypothesis_iff :
    SuslinHypothesis ↔
      ∀ (X : Type) [LinearOrder X] [TopologicalSpace X] [OrderTopology X],
        IsCCC X → SeparableSpace X := by
  constructor
  · intro h X _ _ _ hccc
    by_contra hsep
    exact h X ⟨hccc, hsep⟩
  · intro h X _ _ _ hS
    exact hS.2 (h X hS.1)

/-- The failure of Suslin's Hypothesis is exactly the existence of a ccc non-separable linearly
ordered topological space. -/
