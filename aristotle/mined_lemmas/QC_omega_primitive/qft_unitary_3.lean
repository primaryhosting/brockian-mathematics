import Mathlib

/-!
# Qft Unitary 3
Category: Quantum Computing
Target: QC.qft_unitary_3
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

/-- `omega` is the primitive 8th root of unity `exp (2πi/8)` used by the 3-qubit QFT. -/

theorem qft_unitary_3 : qft3 ∈ Matrix.unitaryGroup (Fin 8) ℂ := by
  have h8 : ((Real.sqrt 8 : ℝ) : ℂ) * ((Real.sqrt 8 : ℝ) : ℂ) = 8 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  have hs : ((Real.sqrt 8 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 8 : ℝ) : ℂ)⁻¹ = (8 : ℂ)⁻¹ := by
    rw [← mul_inv, h8]
  rw [Matrix.mem_unitaryGroup_iff']
  ext j k
  rw [Matrix.mul_apply]
  have hterm : ∀ l : Fin 8, (star qft3) j l * qft3 l k
      = (8 : ℂ)⁻¹ * ((starRingEnd ℂ) (omega ^ (l.val * j.val)) * omega ^ (l.val * k.val)) := by
    intro l
    rw [Matrix.star_apply]
    simp only [qft3, star_mul', Complex.star_def, Complex.conj_ofReal, map_inv₀]
    rw [← hs]
    ring
  simp only [hterm, ← Finset.mul_sum, key_sum, Matrix.one_apply]
  split <;> norm_num

end QC

