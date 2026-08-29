import Mathlib

/-!
# Euler Product Term Ne Zero
Category: Riemann Program
Target: Riemann.zeta.euler_product_term_ne_zero
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

namespace Riemann.zeta

/-- For `s : ℂ` with `1 < s.re` and `p` a prime, the Euler factor `1 - p ^ (-s)` is nonzero.
The proof shows `‖(p : ℂ) ^ (-s)‖ = p ^ (-s.re) < 1`. -/
theorem euler_product_term_ne_zero {s : Complex} (hs : 1 < s.re) {p : ℕ} (hp : Nat.Prime p) :
    (1 - (p : Complex) ^ (-s)) ≠ 0 := by
  have hp2 : 2 ≤ p := hp.two_le
  have hnorm : ‖(p : Complex) ^ (-s)‖ = (p : ℝ) ^ (-s.re) := by
    rw [Complex.norm_natCast_cpow_of_pos (by omega)]
    simp
  have h1 : (p : ℝ) ^ (-s.re) < 1 := by
    apply Real.rpow_lt_one_of_one_lt_of_neg
    · exact_mod_cast lt_of_lt_of_le one_lt_two (by exact_mod_cast hp2)
    · linarith
  intro h
  have hone : (p : Complex) ^ (-s) = 1 := by linear_combination -h
  rw [hone] at hnorm
  simp at hnorm
  rw [← hnorm] at h1
  exact lt_irrefl _ h1

end Riemann.zeta

