import Mathlib

/-!
# Qft Unitary 7
Category: Quantum Computing
Target: QC.qft_unitary_7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open Complex ZMod AddChar Matrix Finset

/-- The `N`-dimensional quantum Fourier transform matrix: the entry in row `j`, column `k` is
`exp (2 π i · j · k / N) / √N`, with rows and columns indexed by `ZMod N`. -/

theorem qftMatrix_mem_unitaryGroup (N : ℕ) [NeZero N] :
    qftMatrix N ∈ Matrix.unitaryGroup (ZMod N) ℂ := by
  classical
  rw [Matrix.mem_unitaryGroup_iff']
  ext j k
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hN : (Real.sqrt N : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    positivity
  have hsq : (Real.sqrt N : ℂ) * (Real.sqrt N : ℂ) = (N : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hNpos.le]; norm_cast
  have key : ∀ m : ZMod N, (star (qftMatrix N) j m) * qftMatrix N m k
      = ((Real.sqrt N : ℂ)⁻¹ * (Real.sqrt N : ℂ)⁻¹) * stdAddChar (m * (k - j)) := by
    intro m
    have hchar : stdAddChar (-(m * j)) * stdAddChar (m * k) = stdAddChar (m * (k - j)) := by
      rw [← AddChar.map_add_eq_mul]; congr 1; ring
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]
    simp only [qftMatrix_apply, star_def, map_mul, conj_stdAddChar]
    rw [show (starRingEnd ℂ) ((Real.sqrt N : ℂ)⁻¹) = (Real.sqrt N : ℂ)⁻¹ by
      simp [← Complex.ofReal_inv]]
    linear_combination ((Real.sqrt N : ℂ)⁻¹ * (Real.sqrt N : ℂ)⁻¹) * hchar
  rw [Finset.sum_congr rfl (fun m _ => key m), ← Finset.mul_sum, sum_stdAddChar_mul]
  by_cases h : j = k
  · subst h
    rw [sub_self, if_pos rfl, if_pos rfl]
    field_simp
    rw [sq, hsq]
  · rw [if_neg (by simpa [sub_eq_zero, eq_comm] using h), if_neg h, mul_zero]

/-- **The 7-qubit quantum Fourier transform matrix is unitary.**
It is the `2 ^ 7 = 128`-dimensional QFT matrix, acting on the state space of 7 qubits. -/
