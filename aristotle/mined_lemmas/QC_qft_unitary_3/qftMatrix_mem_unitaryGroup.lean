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
