import Mathlib

/-!
# Feit Thompson Odd Order
Category: Frontier Abel
Target: Frontier.feit_thompson_odd_order
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- The statement of the Feit–Thompson (odd order) theorem: every finite group of odd
order is solvable. -/

theorem feit_thompson_iff_simple_case : FeitThompsonStatement ↔ OddOrderSimpleIsAbelian := by
  refine ⟨fun hFT G _ _ hodd hsimple a b => ?_, feit_thompson_odd_order⟩
  haveI := hsimple
  haveI := hFT G hodd
  exact mul_comm_of_isSimpleGroup_of_isSolvable a b

/-- Base case: a finite `p`-group is solvable (in particular every group of odd prime power
order is solvable). -/
