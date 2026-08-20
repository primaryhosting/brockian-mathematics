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

lemma star_qftRoot (N : ℕ) : star (qftRoot N) = (qftRoot N)⁻¹ := by
  have hnorm : ‖qftRoot N‖ = 1 := by
    rw [qftRoot]
    rw [show (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))
        = ((2 * Real.pi / N : ℝ) : ℂ) * Complex.I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  rw [Complex.inv_eq_conj hnorm]
  rfl

/-- Orthogonality of the columns of the (unnormalized) DFT matrix. -/
