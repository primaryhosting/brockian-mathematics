import Mathlib

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

namespace QC

/-- The `N × N` discrete Fourier transform (QFT) matrix:
`(QFT)_{j,k} = (1/√N) · exp(2πi·j·k/N)`. -/
noncomputable def qftMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun j k =>
    ((Real.sqrt N : ℝ) : ℂ)⁻¹ *
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((j : ℕ) * (k : ℕ)) / (N : ℂ))

/-- The 3-qubit quantum Fourier transform matrix, of size `2^3 = 8`. -/
noncomputable def qft3 : Matrix (Fin 8) (Fin 8) ℂ := qftMatrix 8

/-- The primitive `N`-th root of unity used by the QFT. -/
noncomputable def qftRoot (N : ℕ) : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))

lemma qftRoot_isPrimitiveRoot (N : ℕ) (hN : N ≠ 0) : IsPrimitiveRoot (qftRoot N) N := by
  have := Complex.isPrimitiveRoot_exp N hN
  simpa [qftRoot, mul_comm, mul_assoc, mul_left_comm] using this

lemma qftRoot_ne_zero (N : ℕ) : qftRoot N ≠ 0 := Complex.exp_ne_zero _

lemma qftMatrix_apply (N : ℕ) (j k : Fin N) :
    qftMatrix N j k = ((Real.sqrt N : ℝ) : ℂ)⁻¹ * (qftRoot N) ^ ((j : ℕ) * (k : ℕ)) := by
  rw [qftMatrix]
  simp only [Matrix.of_apply]
  rw [qftRoot, ← Complex.exp_nat_mul]
  congr 2
  push_cast
  ring

lemma star_qftRoot (N : ℕ) : star (qftRoot N) = (qftRoot N)⁻¹ := by
  have hnorm : ‖qftRoot N‖ = 1 := by
    rw [qftRoot]
    rw [show (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))
        = ((2 * Real.pi / N : ℝ) : ℂ) * Complex.I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  rw [Complex.inv_eq_conj hnorm]
  rfl

/-- Orthogonality of the columns of the (unnormalized) DFT matrix. -/
lemma qftRoot_sum (N : ℕ) (hN : N ≠ 0) (j k : Fin N) :
    ∑ l : Fin N, star ((qftRoot N) ^ ((l : ℕ) * (j : ℕ))) * (qftRoot N) ^ ((l : ℕ) * (k : ℕ))
      = if j = k then (N : ℂ) else 0 := by
  set w := qftRoot N with hw
  have hprim : IsPrimitiveRoot w N := qftRoot_isPrimitiveRoot N hN
  have hwne : w ≠ 0 := qftRoot_ne_zero N
  set z : ℂ := (w⁻¹) ^ (j : ℕ) * w ^ (k : ℕ) with hz
  have hterm : ∀ l : Fin N,
      star (w ^ ((l : ℕ) * (j : ℕ))) * w ^ ((l : ℕ) * (k : ℕ)) = z ^ (l : ℕ) := by
    intro l
    rw [star_pow, star_qftRoot N, ← hw, hz, mul_pow, ← pow_mul, ← pow_mul,
      mul_comm (j : ℕ) (l : ℕ), mul_comm (k : ℕ) (l : ℕ)]
  rw [Finset.sum_congr rfl (fun l _ => hterm l)]
  rw [Fin.sum_univ_eq_sum_range (fun i => z ^ i) N]
  by_cases hjk : j = k
  · subst hjk
    have : z = 1 := by
      rw [hz, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hwne)]
    simp [this]
  · have hz1 : z ≠ 1 := by
      intro h
      apply hjk
      rw [hz, inv_pow, inv_mul_eq_one₀ (pow_ne_zero _ hwne)] at h
      exact Fin.val_injective (hprim.pow_inj j.isLt k.isLt h)
    have hzN : z ^ N = 1 := by
      rw [hz, mul_pow, ← pow_mul, ← pow_mul, mul_comm (j : ℕ) N, mul_comm (k : ℕ) N,
        pow_mul, pow_mul, inv_pow, hprim.pow_eq_one]
      simp
    rw [geom_sum_eq hz1, hzN, sub_self, zero_div, if_neg hjk]

theorem qftMatrix_mem_unitaryGroup (N : ℕ) (hN : N ≠ 0) :
    qftMatrix N ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext j k
  rw [Matrix.mul_apply]
  have hNpos : (0 : ℝ) < N := by positivity
  have hsqrt : ((Real.sqrt N : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt (Real.sqrt_pos.mpr hNpos)
  have hcalc : ∀ l : Fin N, (star (qftMatrix N) j l) * qftMatrix N l k
      = (((Real.sqrt N : ℝ) : ℂ)⁻¹ * ((Real.sqrt N : ℝ) : ℂ)⁻¹) *
        (star ((qftRoot N) ^ ((l : ℕ) * (j : ℕ))) * (qftRoot N) ^ ((l : ℕ) * (k : ℕ))) := by
    intro l
    have : star (qftMatrix N) j l = star (qftMatrix N l j) := rfl
    rw [this, qftMatrix_apply, qftMatrix_apply, star_mul']
    have : star (((Real.sqrt N : ℝ) : ℂ)⁻¹) = ((Real.sqrt N : ℝ) : ℂ)⁻¹ := by
      simp [← Complex.ofReal_inv]
    rw [this]
    ring
  rw [Finset.sum_congr rfl (fun l _ => hcalc l), ← Finset.mul_sum, qftRoot_sum N hN]
  have hsq : ((Real.sqrt N : ℝ) : ℂ)⁻¹ * ((Real.sqrt N : ℝ) : ℂ)⁻¹ = ((N : ℂ))⁻¹ := by
    rw [← mul_inv, ← Complex.ofReal_mul, ← Real.sqrt_mul_self (le_of_lt hNpos)]
    norm_num
  rw [hsq]
  by_cases hjk : j = k
  · subst hjk
    have hNne : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
    simp [hNne]
  · simp [hjk]

/-- **The 3-qubit quantum Fourier transform matrix is unitary.** -/
theorem qft_unitary_3 : qft3 ∈ Matrix.unitaryGroup (Fin 8) ℂ :=
  qftMatrix_mem_unitaryGroup 8 (by norm_num)

end QC

