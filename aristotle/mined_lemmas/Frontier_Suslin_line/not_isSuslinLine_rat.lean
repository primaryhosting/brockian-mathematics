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

theorem not_isSuslinLine_rat : ¬ IsSuslinLine ℚ :=
  not_isSuslinLine_of_separableSpace

/-! ## The base case of the reduction of a Suslin line to a Suslin tree -/

/-- **Base step of the Suslin-tree construction.**  In a densely ordered Suslin line, for every
countable set `C` there is a nonempty open interval avoiding `C`.  (Iterating this along `ω₁` is
the classical construction of a Suslin tree from a Suslin line.) -/
