/-
# Qft Unitary 8
Category: Quantum Computing
Target: QC.qft_unitary_8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Qft Unitary 8
Category: Quantum Computing
Target: QC.qft_unitary_8
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QC

/-- The primitive `n`-th root of unity `exp (2πi/n)`. -/

lemma star_omegaRoot (n : ℕ) : star (omegaRoot n) = (omegaRoot n)⁻¹ := by
  have hnorm : ‖omegaRoot n‖ = 1 := by
    rw [omegaRoot, Complex.norm_exp]
    have : (2 * (Real.pi : ℂ) * Complex.I / (n : ℂ)).re = 0 := by
      simp [Complex.div_re, Complex.mul_re, Complex.mul_im]
    rw [this, Real.exp_zero]
  rw [Complex.inv_eq_conj hnorm]
  rfl

/-- The key orthogonality relation: a nontrivial power of `omegaRoot n` sums to zero over
a full period. -/
