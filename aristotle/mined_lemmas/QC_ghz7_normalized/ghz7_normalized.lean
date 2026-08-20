import Mathlib

/-!
# Ghz 7 Normalized
Category: Quantum Computing
Target: QC.ghz7_normalized
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

set_option grind.warning false

namespace QC

/-- Computational basis states of 7 qubits: functions `Fin 7 → Bool`. -/
abbrev Qubits7 := Fin 7 → Bool

/-- The all-zeros basis state `|0000000⟩`. -/

theorem ghz7_normalized : ‖ghz7‖ = 1 := by
  rw [EuclideanSpace.norm_eq,
    Finset.sum_eq_add allZero allOne allZero_ne_allOne
      (by intro c _ hc; simp [ghz7, hc.1, hc.2]) (by intro h; simp at h) (by intro h; simp at h)]
  have h2 : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  simp [ghz7, Complex.norm_real, abs_of_pos h2, ← Real.sqrt_inv]
  norm_num

end QC

