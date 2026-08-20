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

theorem uncountable_of_isSuslinLine (h : IsSuslinLine X) : Uncountable X := by
  rw [← not_countable_iff]
  intro hc
  haveI : Countable X := hc
  exact h.2 ⟨⟨Set.univ, Set.countable_univ, dense_univ⟩⟩

/-- A Suslin line is not second countable. -/
