/-
# Strong Subadditivity
Category: Frontier Qi
Target: QI.strong_subadditivity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Lean requires `import` commands to precede any module docstring, so the header above is
repeated as a module docstring below the import.)
-/

import Mathlib

/-!
# Strong Subadditivity
Category: Frontier Qi
Target: QI.strong_subadditivity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix Real Finset

namespace QI

/-! ## Von Neumann entropy -/

open scoped Classical in
/-- The von Neumann entropy `S(ρ) = -Tr(ρ log ρ)` of a Hermitian matrix, computed as
`∑ i, negMulLog (λ i)` over the eigenvalues of `ρ`. (Junk value `0` for non-Hermitian input.) -/

theorem sub_le_mul_log_div {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (h : u ≠ 0 → v ≠ 0) :
    u - v ≤ u * Real.log (u / v) := by
  rcases eq_or_lt_of_le hu with hu0 | hu0
  · simp [← hu0]; linarith
  · have hv0 : 0 < v := lt_of_le_of_ne hv (Ne.symm (h (ne_of_gt hu0)))
    have h1 : Real.log (v / u) ≤ v / u - 1 := Real.log_le_sub_one_of_pos (by positivity)
    have h2 : Real.log (u / v) = -Real.log (v / u) := by
      rw [← Real.log_inv]; congr 1; field_simp
    have h3 : u * (v / u - 1) = v - u := by field_simp
    rw [h2]
    nlinarith [h1]

/-- The auxiliary (subnormalised) distribution `q(a,b,c) = p(a,b) p(b,c) / p(b)`. -/
