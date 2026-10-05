import Mathlib
/-!
# Iit Phi Partition
Category: Frontier Mind
Target: Frontier.iit_phi_partition
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-! ## A finite-sum Gibbs inequality

The nonnegativity of a Kullback–Leibler divergence between two finitely supported
probability distributions. -/

/-- One term of Gibbs' inequality: `p - q ≤ p * log (p / q)`, under the absolute
continuity assumption `q = 0 → p = 0`. -/

theorem gibbs_term {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hac : q = 0 → p = 0) :
    p - q ≤ p * Real.log (p / q) := by
  rcases eq_or_lt_of_le hp with hp0 | hp0
  · simp [← hp0]
    linarith
  · have hq0 : 0 < q := by
      rcases eq_or_lt_of_le hq with h | h
      · exact absurd (hac h.symm) (by linarith)
      · exact h
    have hlog : Real.log (q / p) ≤ q / p - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have hinv : Real.log (p / q) = -Real.log (q / p) := by
      rw [← Real.log_inv]
      congr 1
      field_simp
    rw [hinv]
    have hmul : p * (q / p - 1) = q - p := by field_simp
    nlinarith [hlog, hp0]

/-- Gibbs' inequality (nonnegativity of the discrete Kullback–Leibler divergence). -/
