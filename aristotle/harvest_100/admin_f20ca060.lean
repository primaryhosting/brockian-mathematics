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

/-- For `s : ℂ` with `1 < s.re` and `p` a prime, the Euler factor `1 - p ^ (-s)`
is nonzero.  Indeed `‖(p : ℂ) ^ (-s)‖ = p ^ (-s.re) < 1`, so `p ^ (-s) ≠ 1`. -/
theorem euler_product_term_ne_zero {s : ℂ} (hs : 1 < s.re) {p : ℕ} (hp : p.Prime) :
    (1 - (p : ℂ) ^ (-s)) ≠ 0 := by
  have hnorm : ‖(p : ℂ) ^ (-s)‖ = (p : ℝ) ^ (-s).re :=
    Complex.norm_natCast_cpow_of_pos hp.pos _
  intro hc
  have h1 : (p : ℂ) ^ (-s) = 1 := by linear_combination -hc
  rw [h1, norm_one] at hnorm
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hlt : (p : ℝ) ^ (-s).re < 1 := by
    refine Real.rpow_lt_one_of_one_lt_of_neg (by linarith) ?_
    simp only [Complex.neg_re]
    linarith
  linarith

end Riemann.zeta

