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

/-
# Qft Unitary
Category: Quantum Computing
Target: QC.qft_unitary
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Qft Unitary
Category: Quantum Computing
Target: QC.qft_unitary
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open Complex Finset

/-- The primitive `N`-th root of unity `exp (2 π i / N)`. -/

lemma dft_mul_star_term {N : ℕ} (j l k : Fin N) :
    dftMatrix N j k * (star (dftMatrix N)) k l
      = ((zeta N) ^ ((j.val : ℤ) - (l.val : ℤ))) ^ k.val / (N : ℂ) := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · exact absurd k.isLt (by omega)
  have hNR : (0:ℝ) < N := by positivity
  have hc : ((Real.sqrt N : ℝ) : ℂ) * ((Real.sqrt N : ℝ) : ℂ) = (N : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hNR.le, Complex.ofReal_natCast]
  rw [Matrix.star_apply, dftMatrix_apply, dftMatrix_apply, zeta_zpow_pow, star_div₀, star_pow,
    Complex.star_def, zeta_conj, Complex.conj_ofReal, inv_pow, ← hc]
  field_simp

/-- Orthogonality relation: the geometric sum of the powers of `zeta N ^ (j - l)`
is `N` when `j = l` and `0` otherwise. -/
