import Mathlib

/-!
# Paris Harrington
Category: Frontier — Set Theory
Target: Frontier.Paris_Harrington
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Set

namespace Frontier

/-! ## Basic notions -/

/-- A finite set of naturals is *relatively large* when it is nonempty and its cardinality
is at least its least element. -/

theorem chainElt_lt_succ (n : ℕ) : chainElt U D k n < chainElt U D k (n + 1) := by
  refine lt_chainElt U D k hU hD (n + 1) _ ?_
  rw [chain_succ]
  exact Finset.mem_insert_self _ _

