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

theorem not_secondCountable_of_isSuslinLine (h : IsSuslinLine X) :
    ¬ SecondCountableTopology X := by
  intro hsc
  exact h.2 (by haveI := hsc; infer_instance)

/-- The real line is not a Suslin line. -/
