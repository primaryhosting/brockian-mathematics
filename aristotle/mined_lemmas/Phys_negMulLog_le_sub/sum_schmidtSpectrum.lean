import Mathlib
/-!
# Area Law 1 D
Category: Frontier Phys
Target: Phys.area_law_1d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on file layout: Lean 4 requires `import` to be the very first command of a module, so the
requested header block appears immediately after the single `import Mathlib` line.
-/

open scoped BigOperators ComplexOrder
open Matrix

namespace Phys

/-! ## Elementary entropy inequalities -/

/-- Gibbs-type pointwise bound: for `x ≥ 0` and a reference weight `r > 0`,
`-x log x ≤ (r - x) - x log r`. -/

theorem sum_schmidtSpectrum (psi : Matrix A B ℂ) (hnorm : (psi * psiᴴ).trace = 1) :
    ∑ i, schmidtSpectrum psi i = 1 := by
  have h := (Matrix.isHermitian_mul_conjTranspose_self psi).trace_eq_sum_eigenvalues
  rw [hnorm] at h
  have h2 : ((∑ i, schmidtSpectrum psi i : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
    simp only [schmidtSpectrum]
    push_cast
    exact h.symm
  exact_mod_cast h2

/-- Sorting a spectrum: truncation bounds by arbitrary index sets are equivalent to tail bounds
for the nonincreasing rearrangement. -/
