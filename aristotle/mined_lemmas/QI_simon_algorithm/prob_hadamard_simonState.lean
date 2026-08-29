import Mathlib

/-!
# Simon Algorithm
Category: Frontier Qi
Target: QI.simon_algorithm
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

namespace QI

/-! ## The Boolean cube as an `𝔽₂`-vector space -/

/-- `n`-bit strings, viewed as the elementary abelian 2-group `(ℤ/2)ⁿ`;
addition is bitwise XOR. -/
abbrev V (n : ℕ) : Type := Fin n → ZMod 2


lemma prob_hadamard_simonState {n : ℕ} (s x0 y : V n) (hs : s ≠ 0) (h : dotp s y = 0) :
    ‖hadamard (simonState s x0) y‖ ^ 2 = 2 / 2 ^ n := by
  have hsq : Real.sqrt (2 ^ n) ^ 2 = (2 : ℝ) ^ n := Real.sq_sqrt (by positivity)
  have hsq2 : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hpos : (0 : ℝ) < Real.sqrt (2 ^ n) := Real.sqrt_pos.mpr (by positivity)
  have hpos2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  rw [hadamard_simonState s x0 y hs, dotp_add_left, h, add_zero]
  have hrw : ∀ a : ℂ, (((Real.sqrt (2 ^ n))⁻¹ : ℝ) : ℂ) * ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (a + a))
      = (((Real.sqrt (2 ^ n))⁻¹ * (Real.sqrt 2)⁻¹ * 2 : ℝ) : ℂ) * a := by
    intro a
    push_cast
    ring
  rw [hrw, norm_mul, norm_sgn, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]
  field_simp
  nlinarith [hsq, hsq2, hpos, hpos2]

/-! ## `O(n)` samples determine the hidden shift -/

/-- **The post-processing of Simon's algorithm succeeds with `O(n)` samples.**
For every nonzero shift `s` there is a set of at most `n` vectors `Y ⊆ s^⊥` whose common
orthogonal complement is exactly `{0, s}`; hence `n` measurement outcomes suffice to pin
down `s`, i.e. Simon's problem is solved with `O(n)` quantum queries. -/
