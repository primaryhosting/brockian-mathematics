import Mathlib

/-!
# Twist Partial Sum Norm Le
Category: Characters
Target: Brockian.Characters5.twistPartialSum_norm_le
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

namespace Brockian
namespace Characters5

/-- The primitive fifth root of unity `ω = e^{2πi/5}`. -/

lemma omega_ne_one : omega ≠ 1 := by
  rw [omega, Ne, Complex.exp_eq_one_iff]
  rintro ⟨n, hn⟩
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  field_simp at hn
  have hz : ((1 : ℤ) : ℂ) = ((5 * n : ℤ) : ℂ) := by push_cast; linear_combination hn
  have hint : (1 : ℤ) = 5 * n := by exact_mod_cast hz
  omega

/-- The full period sum vanishes: `∑_{j<5} ω^j = 0`. -/
