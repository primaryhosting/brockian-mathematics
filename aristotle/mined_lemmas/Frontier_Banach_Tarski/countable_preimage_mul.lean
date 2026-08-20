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

theorem countable_preimage_mul {n : ℕ} (hn : 0 < n) {S : Set ℝ} (hS : S.Countable) :
    {t : ℝ | (n : ℝ) * t ∈ S}.Countable := by
  have hinj : Function.Injective fun t : ℝ => (n : ℝ) * t := by
    intro a b hab
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    exact mul_left_cancel₀ hn' hab
  exact hS.preimage hinj

/-- A rotation about the `z`-axis whose iterates move a countable set avoiding the `z`-axis
off itself. -/
