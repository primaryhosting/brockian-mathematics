import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped Matrix

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

namespace QC

/-- `QC.zeta N m = exp (2 π i m / N)`, the `m`-th power of the primitive `N`-th root of unity
used to define the quantum Fourier transform. -/
noncomputable def zeta (N : ℕ) (m : ℤ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) / (N : ℂ))

/-- The quantum Fourier transform matrix on `N` basis states:
`(QFT_N) j k = N^(-1/2) * exp (2 π i j k / N)`. -/
noncomputable def qftMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  fun j k => ((Real.sqrt N : ℝ) : ℂ)⁻¹ *
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((j : ℕ) : ℂ) * ((k : ℕ) : ℂ) / (N : ℂ))

/-- The quantum Fourier transform on `n` qubits, a `2^n × 2^n` complex matrix. -/
noncomputable def qft (n : ℕ) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ := qftMatrix (2 ^ n)

lemma zeta_add (N : ℕ) (a b : ℤ) : zeta N (a + b) = zeta N a * zeta N b := by
  unfold zeta
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma zeta_zero (N : ℕ) : zeta N 0 = 1 := by
  simp [zeta]

lemma zeta_pow (N : ℕ) (m : ℤ) (l : ℕ) : zeta N m ^ l = zeta N (m * l) := by
  induction l with
  | zero => simp [zeta_zero]
  | succ l ih =>
      rw [pow_succ, ih, ← zeta_add]
      congr 1
      push_cast
      ring

lemma zeta_conj (N : ℕ) (m : ℤ) : (starRingEnd ℂ) (zeta N m) = zeta N (-m) := by
  unfold zeta
  rw [← Complex.exp_conj]
  congr 1
  simp [Complex.ext_iff]

lemma zeta_ne_one {N : ℕ} {m : ℤ} (hm : m ≠ 0) (hlt : m.natAbs < N) : zeta N m ≠ 1 := by
  have hN : (0:ℕ) < N := lt_of_le_of_lt (Nat.zero_le _) hlt
  intro h
  rw [zeta, Complex.exp_eq_one_iff] at h
  obtain ⟨t, ht⟩ := h
  have hπ : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hz : m = (N : ℤ) * t := by
    field_simp at ht
    exact_mod_cast ht
  have ht0 : t ≠ 0 := by
    rintro rfl
    simp at hz
    exact hm hz
  have habs : m.natAbs = N * t.natAbs := by
    rw [hz, Int.natAbs_mul]
    simp
  have h1 : 1 ≤ t.natAbs := Int.natAbs_pos.mpr ht0
  have : N ≤ N * t.natAbs := Nat.le_mul_of_pos_right N h1
  omega

/-- The key orthogonality relation: the geometric sum of powers of `zeta N m` over a full period
is `N` when `m = 0` and `0` otherwise (for `|m| < N`). -/
lemma sum_zeta_pow {N : ℕ} {m : ℤ} (hm : m.natAbs < N) :
    ∑ l ∈ Finset.range N, zeta N m ^ l = if m = 0 then (N : ℂ) else 0 := by
  by_cases h : m = 0
  · subst h
    simp [zeta_zero]
  · rw [if_neg h]
    have hne : zeta N m ≠ 1 := zeta_ne_one h hm
    rw [geom_sum_eq hne]
    have hpow : zeta N m ^ N = 1 := by
      rw [zeta_pow, zeta]
      rw [Complex.exp_eq_one_iff]
      refine ⟨m, ?_⟩
      have hN : (0:ℕ) < N := lt_of_le_of_lt (Nat.zero_le _) hm
      have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
      field_simp
      push_cast
      ring
    rw [hpow]
    simp

lemma qftMatrix_apply (N : ℕ) (j k : Fin N) :
    qftMatrix N j k = ((Real.sqrt N : ℝ) : ℂ)⁻¹ * zeta N ((j : ℕ) * (k : ℕ) : ℤ) := by
  unfold qftMatrix zeta
  congr 2
  push_cast
  ring

lemma inv_sqrt_sq {N : ℕ} (hN : 0 < N) :
    ((Real.sqrt N : ℝ) : ℂ)⁻¹ * ((Real.sqrt N : ℝ) : ℂ)⁻¹ = ((N : ℂ))⁻¹ := by
  have h : (Real.sqrt N : ℝ) * (Real.sqrt N : ℝ) = (N : ℝ) :=
    Real.mul_self_sqrt (by positivity)
  have : ((Real.sqrt N : ℝ) : ℂ) * ((Real.sqrt N : ℝ) : ℂ) = (N : ℂ) := by
    exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) h
  rw [← mul_inv, this]

lemma conjTranspose_mul_self (N : ℕ) (hN : 0 < N) :
    (qftMatrix N)ᴴ * qftMatrix N = 1 := by
  ext j k
  rw [Matrix.mul_apply]
  have key : ∀ l : Fin N, (qftMatrix N)ᴴ j l * qftMatrix N l k
      = ((N : ℂ))⁻¹ * zeta N (((k : ℕ) : ℤ) - ((j : ℕ) : ℤ)) ^ (l : ℕ) := by
    intro l
    rw [Matrix.conjTranspose_apply, qftMatrix_apply, qftMatrix_apply, Complex.star_def,
      map_mul, zeta_conj]
    have hr : (starRingEnd ℂ) ((Real.sqrt N : ℝ) : ℂ)⁻¹ = ((Real.sqrt N : ℝ) : ℂ)⁻¹ := by
      simp [← Complex.ofReal_inv]
    rw [hr, zeta_pow]
    rw [mul_mul_mul_comm, inv_sqrt_sq hN, ← zeta_add]
    congr 2
    ring
  rw [Finset.sum_congr rfl (fun l _ => key l)]
  rw [← Finset.mul_sum]
  have : ∑ l : Fin N, zeta N (((k : ℕ) : ℤ) - ((j : ℕ) : ℤ)) ^ (l : ℕ)
      = ∑ l ∈ Finset.range N, zeta N (((k : ℕ) : ℤ) - ((j : ℕ) : ℤ)) ^ l :=
    Fin.sum_univ_eq_sum_range (fun l => zeta N (((k : ℕ) : ℤ) - ((j : ℕ) : ℤ)) ^ l) N
  rw [this]
  have hlt : (((k : ℕ) : ℤ) - ((j : ℕ) : ℤ)).natAbs < N := by
    have hk := k.isLt
    have hj := j.isLt
    omega
  rw [sum_zeta_pow hlt]
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  by_cases hjk : j = k
  · subst hjk
    simp [hNc]
  · have : (((k : ℕ) : ℤ) - ((j : ℕ) : ℤ)) ≠ 0 := by
      simp only [sub_ne_zero]
      intro h
      exact hjk (Fin.ext (by exact_mod_cast h.symm))
    rw [if_neg this]
    simp [hjk]

lemma self_mul_conjTranspose (N : ℕ) (hN : 0 < N) :
    qftMatrix N * (qftMatrix N)ᴴ = 1 := by
  have h := conjTranspose_mul_self N hN
  exact mul_eq_one_comm.mp h

/-- **The 6-qubit quantum Fourier transform matrix is unitary.** -/
theorem qft_unitary_6 : qft 6 ∈ unitary (Matrix (Fin (2 ^ 6)) (Fin (2 ^ 6)) ℂ) := by
  have hN : 0 < 2 ^ 6 := by norm_num
  refine ⟨?_, ?_⟩
  · rw [Matrix.star_eq_conjTranspose]
    exact conjTranspose_mul_self _ hN
  · rw [Matrix.star_eq_conjTranspose]
    exact self_mul_conjTranspose _ hN

end QC

#print axioms QC.qft_unitary_6

