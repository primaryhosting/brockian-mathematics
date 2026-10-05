import Mathlib

/-!
# Qft Unitary 6
Category: Quantum Computing
Target: QC.qft_unitary_6
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

/-- The `N × N` discrete Fourier transform (QFT) matrix:
`F j k = exp (2 π i j k / N) / √N`. -/
noncomputable def dftMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℂ := fun j k =>
  Complex.exp (2 * Real.pi * Complex.I * (j.val * k.val) / N) / Real.sqrt N

/-- The quantum Fourier transform matrix on `n` qubits, of size `2 ^ n`. -/
noncomputable def qftMatrix (n : ℕ) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  dftMatrix (2 ^ n)

/-- The primitive `N`-th root of unity used by the DFT. -/
noncomputable def omegaN (N : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / N)

lemma dftMatrix_apply (N : ℕ) (j k : Fin N) :
    dftMatrix N j k = omegaN N ^ (j.val * k.val) / Real.sqrt N := by
  have harg : (2 * (Real.pi : ℂ) * Complex.I * ((j.val : ℂ) * (k.val : ℂ)) / (N : ℂ))
      = ((j.val * k.val : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ)) := by
    push_cast
    ring
  rw [dftMatrix, omegaN, ← Complex.exp_nat_mul, ← harg]

lemma omegaN_pow_N (N : ℕ) (hN : N ≠ 0) : omegaN N ^ N = 1 :=
  (Complex.isPrimitiveRoot_exp N hN).pow_eq_one

lemma omegaN_ne_zero (N : ℕ) : omegaN N ≠ 0 := Complex.exp_ne_zero _

/-- Column orthogonality of the DFT matrix. -/
lemma dft_col_orthogonal (N : ℕ) (hN : N ≠ 0) (j k : Fin N) :
    ∑ m : Fin N, (starRingEnd ℂ) (omegaN N ^ (m.val * j.val)) * omegaN N ^ (m.val * k.val)
      = if j = k then (N : ℂ) else 0 := by
  have hprim := Complex.isPrimitiveRoot_exp N hN
  set w : ℂ := omegaN N with hw
  have hwne : w ≠ 0 := omegaN_ne_zero N
  have hconj : (starRingEnd ℂ) w = w⁻¹ := by
    rw [hw, omegaN, ← Complex.exp_conj, ← Complex.exp_neg]
    congr 1
    simp only [map_div₀, map_mul, map_ofNat, Complex.conj_I, Complex.conj_ofReal, map_natCast]
    ring
  have hterm : ∀ m : Fin N,
      (starRingEnd ℂ) (w ^ (m.val * j.val)) * w ^ (m.val * k.val)
        = (w ^ ((k.val : ℤ) - (j.val : ℤ))) ^ (m.val : ℕ) := by
    intro m
    rw [map_pow, hconj, inv_pow, ← zpow_natCast w (m.val * j.val), ← zpow_natCast w (m.val * k.val),
      ← zpow_neg, ← zpow_natCast (w ^ ((k.val : ℤ) - (j.val : ℤ))) m.val, ← zpow_mul,
      ← zpow_add₀ hwne]
    congr 1
    push_cast
    ring
  simp_rw [hterm]
  set x : ℂ := w ^ ((k.val : ℤ) - (j.val : ℤ)) with hx
  rw [Fin.sum_univ_eq_sum_range (fun m => x ^ m) N]
  by_cases hjk : j = k
  · subst hjk
    have : x = 1 := by simp [hx]
    simp [this]
  · have hxne : x ≠ 1 := by
      rw [hx]
      intro h
      have hdvd : (N : ℤ) ∣ ((k.val : ℤ) - (j.val : ℤ)) := (hprim.zpow_eq_one_iff_dvd _).mp h
      have hd : N ∣ ((k.val : ℤ) - (j.val : ℤ)).natAbs := by
        simpa using Int.natAbs_dvd_natAbs.mpr hdvd
      have hne : j.val ≠ k.val := fun h2 => hjk (Fin.ext h2)
      have hj := j.isLt
      have hk := k.isLt
      have hpos : 0 < ((k.val : ℤ) - (j.val : ℤ)).natAbs := by omega
      have := Nat.le_of_dvd hpos hd
      omega
    have hxN : x ^ N = 1 := by
      rw [hx, ← zpow_natCast (w ^ _) N, ← zpow_mul, mul_comm, zpow_mul,
        zpow_natCast, omegaN_pow_N N hN, one_zpow]
    rw [geom_sum_eq hxne, hxN, sub_self, zero_div]
    simp [hjk]

theorem dft_unitary (N : ℕ) (hN : N ≠ 0) : dftMatrix N ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext j k
  rw [Matrix.mul_apply]
  have hNpos : (0:ℝ) < N := by positivity
  have hsq : ((Real.sqrt N : ℝ) : ℂ) * ((Real.sqrt N : ℝ) : ℂ) = (N : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (le_of_lt hNpos)]
    simp
  have key := dft_col_orthogonal N hN j k
  have hterm : ∀ m : Fin N, star (dftMatrix N) j m * dftMatrix N m k
      = ((starRingEnd ℂ) (omegaN N ^ (m.val * j.val)) * omegaN N ^ (m.val * k.val))
        / (N : ℂ) := by
    intro m
    rw [Matrix.star_apply, dftMatrix_apply, dftMatrix_apply, Complex.star_def, map_div₀,
      Complex.conj_ofReal, div_mul_div_comm, hsq]
  simp_rw [hterm, ← Finset.sum_div, key]
  by_cases hjk : j = k
  · subst hjk
    have hNne : (N : ℂ) ≠ 0 := by exact_mod_cast hN
    simp [hNne]
  · simp [hjk]

/-- The 6-qubit quantum Fourier transform matrix is unitary. -/
theorem qft_unitary_6 : qftMatrix 6 ∈ Matrix.unitaryGroup (Fin (2 ^ 6)) ℂ :=
  dft_unitary (2 ^ 6) (by norm_num)

end QC

#print axioms QC.qft_unitary_6

