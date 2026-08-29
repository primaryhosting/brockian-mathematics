/-
# Euler Product Term Ne Zero
Category: Riemann Program
Target: Riemann.zeta.euler_product_term_ne_zero
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Riemann
namespace zeta

/-- For `s : ℂ` with `1 < s.re` and `p` a prime, the Euler factor `1 - p ^ (-s)`
is nonzero.  Indeed `‖p ^ (-s)‖ = p ^ (-s.re) < 1` since `p ≥ 2` and `s.re > 1`,
so `p ^ (-s) ≠ 1`. -/
theorem euler_product_term_ne_zero (s : ℂ) (hs : 1 < s.re) (p : ℕ) (hp : Nat.Prime p) :
    (1 - (p : ℂ) ^ (-s)) ≠ 0 := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hcast : ((p : ℝ) : ℂ) = (p : ℂ) := by push_cast; ring
  have hnorm : ‖(p : ℂ) ^ (-s)‖ = (p : ℝ) ^ (-s.re) := by
    rw [← hcast, Complex.norm_cpow_eq_rpow_re_of_pos hp0]
    simp
  have hlt : ‖(p : ℂ) ^ (-s)‖ < 1 := by
    rw [hnorm]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by linarith)
  intro h
  have h1 : (p : ℂ) ^ (-s) = 1 := by linear_combination -h
  rw [h1] at hlt
  simp at hlt

end zeta
end Riemann

