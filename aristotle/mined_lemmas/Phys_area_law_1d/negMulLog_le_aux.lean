/-
# Area Law 1 D
Category: Frontier Phys
Target: Phys.area_law_1d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Lean requires `import` to precede any module docstring, so the header above is a plain
comment and is repeated verbatim as the module docstring below.)
-/

import Mathlib

/-!
# Area Law 1 D
Category: Frontier Phys
Target: Phys.area_law_1d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Phys

open Real Finset

/-- A **Schmidt spectrum** across a cut of a one–dimensional chain: the (squared) Schmidt
coefficients `p i` of a pure state with respect to a bipartition `A ∣ B`.  Equivalently, the
eigenvalue distribution of the reduced density matrix `ρ_A`.  Only finitely many coefficients
are non-zero; `support` is a finite set carrying them, and its cardinality bounds the
Schmidt rank (= the bond dimension needed to cut the state at this position). -/
structure SchmidtSpectrum (ι : Type*) where
  /-- The squared Schmidt coefficients, i.e. the eigenvalues of the reduced density matrix. -/
  p : ι → ℝ
  /-- A finite set containing all indices with non-zero weight. -/
  support : Finset ι
  /-- Eigenvalues of a density matrix are non-negative. -/
  nonneg : ∀ i, 0 ≤ p i
  /-- Outside the support the weights vanish. -/
  vanish : ∀ i ∉ support, p i = 0
  /-- The reduced density matrix has unit trace. -/
  total : ∑ i ∈ support, p i = 1

namespace SchmidtSpectrum

variable {ι : Type*} (σ : SchmidtSpectrum ι)

/-- The **entanglement entropy** (von Neumann entropy of the reduced density matrix)
`S(ρ_A) = -∑ᵢ pᵢ log pᵢ`. -/

lemma negMulLog_le_aux {p : ℝ} (hp : 0 ≤ p) {N : ℝ} (hN : 0 < N) :
    Real.negMulLog p ≤ p * Real.log N + 1 / N - p := by
  rcases eq_or_lt_of_le hp with h | hp'
  · simp only [← h, Real.negMulLog_zero, zero_mul, zero_add, sub_zero]
    positivity
  · have hx : 0 < 1 / (p * N) := by positivity
    have hlog := Real.log_le_sub_one_of_pos hx
    have hmul : p * Real.log (1 / (p * N)) ≤ p * (1 / (p * N) - 1) :=
      mul_le_mul_of_nonneg_left hlog hp
    have hrw : Real.log (1 / (p * N)) = -(Real.log p + Real.log N) := by
      rw [Real.log_div one_ne_zero (by positivity), Real.log_mul (ne_of_gt hp') (ne_of_gt hN)]
      simp
    have hval : p * (1 / (p * N) - 1) = 1 / N - p := by
      field_simp
    rw [hrw, hval] at hmul
    have : Real.negMulLog p = -(p * Real.log p) := by
      rw [Real.negMulLog_def]; ring
    nlinarith [hmul]

/-- **Maximum-entropy bound.**  The entanglement entropy is at most the logarithm of the
Schmidt rank across the cut. -/
