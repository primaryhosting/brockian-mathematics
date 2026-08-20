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

theorem not_isSuslinLine_of_separableSpace [SeparableSpace X] : ¬ IsSuslinLine X := by
  rintro ⟨-, h⟩
  exact h ‹SeparableSpace X›

/-- A Suslin line is uncountable. -/
