import Mathlib
/-!
# Cycle Fiedler Value
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_fiedler_value
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

namespace Frontier.Spectral

open Finset Matrix SimpleGraph

/-- The angle `2π/n` for the cycle `C_n` with `n = m + 3`. -/

lemma cos_le_cos_cycAngle {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k < m + 3) :
    Real.cos (k * cycAngle m) ≤ Real.cos (cycAngle m) := by
  have hpos : 0 < cycAngle m := cycAngle_pos
  have hmul : ((m : ℝ) + 3) * cycAngle m = 2 * Real.pi := cycAngle_mul
  have hk1' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
  have hk2' : (k : ℝ) + 1 ≤ (m : ℝ) + 3 := by exact_mod_cast hk2
  have hlow : cycAngle m ≤ (k : ℝ) * cycAngle m := by nlinarith
  have hhigh : (k : ℝ) * cycAngle m ≤ 2 * Real.pi - cycAngle m := by nlinarith
  rcases le_or_gt ((k : ℝ) * cycAngle m) Real.pi with h | h
  · exact Real.cos_le_cos_of_nonneg_of_le_pi hpos.le h hlow
  · rw [← Real.cos_two_pi_sub ((k : ℝ) * cycAngle m)]
    exact Real.cos_le_cos_of_nonneg_of_le_pi hpos.le (by linarith) (by linarith)

end

/-- **Fiedler value of the cycle graph.**  For `n ≥ 3`, the algebraic connectivity of the
cycle graph `C_n`, i.e. the smallest eigenvalue of its Laplacian matrix admitting an
eigenvector orthogonal to the all-ones vector (equivalently, the second-smallest Laplacian
eigenvalue, since `C_n` is connected), equals `2 - 2 cos (2π/n)`. -/
