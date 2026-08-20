/-
# Qft Unitary 8
Category: Quantum Computing
Target: QC.qft_unitary_8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Finset Complex Real ZMod AddChar

namespace QC

/-- The `N × N` quantum Fourier transform matrix, indexed by `ZMod N`:
its `(j, k)` entry is `exp (2 π i j k / N) / √N`. -/

theorem qftMatrix_unitary (N : ℕ) [NeZero N] :
    qftMatrix N ∈ Matrix.unitaryGroup (ZMod N) ℂ := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_neZero N)
  have hsq : ((Real.sqrt N : ℂ)) * ((Real.sqrt N : ℂ)) = (N : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hN.le]; simp
  have hne : ((Real.sqrt N : ℂ)) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero, Real.sqrt_eq_zero', not_le]
    exact hN
  have hs : ((Real.sqrt N : ℂ))⁻¹ * ((Real.sqrt N : ℂ))⁻¹ * (N : ℂ) = 1 := by
    rw [← hsq]; field_simp
  rw [Matrix.mem_unitaryGroup_iff']
  ext j l
  rw [Matrix.mul_apply]
  have key : ∀ k : ZMod N, (star (qftMatrix N)) j k * qftMatrix N k l
      = (Real.sqrt N : ℂ)⁻¹ * (Real.sqrt N : ℂ)⁻¹ * ZMod.stdAddChar (k * (l - j)) := by
    intro k
    have h1 : (starRingEnd ℂ) ((Real.sqrt N : ℂ)⁻¹) = (Real.sqrt N : ℂ)⁻¹ := by simp
    have hchar : ZMod.stdAddChar (-(k * j)) * ZMod.stdAddChar (k * l)
        = ZMod.stdAddChar (k * (l - j)) := by
      rw [← AddChar.map_add_eq_mul]; congr 1; ring
    rw [Matrix.star_apply, RCLike.star_def, qftMatrix_apply, qftMatrix_apply, map_mul,
      conj_stdAddChar, h1, ← hchar]
    ring
  rw [Finset.sum_congr rfl (fun k _ => key k), ← Finset.mul_sum, sum_stdAddChar]
  rcases eq_or_ne j l with h | h
  · simp [h, hs, Matrix.one_apply]
  · rw [if_neg (by simpa [sub_eq_zero, eq_comm] using h)]
    simp [h]

/-- The 8-qubit quantum Fourier transform matrix (of size `2^8 = 256`) is unitary. -/
