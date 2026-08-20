import RequestProject.BT.Ball

/-!
# Banach Tarski
Category: Frontier — Set Theory
Target: Frontier.Banach_Tarski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Metric Set
open scoped Pointwise

namespace Frontier

/-- The vector by which the second copy of the ball is translated. -/

theorem gCenter_pow_zero_ne (n : ℕ) (hn : 0 < n) : (gCenter ^ n) 0 ≠ 0 := by
  rw [gCenter_pow_apply n]
  intro h
  exact rotZ_pHalf_ne n hn (by
    have := sub_eq_zero.1 h
    exact this.symm)

