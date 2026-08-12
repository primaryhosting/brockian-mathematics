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

namespace Riemann.zeta

/-- For a complex number `s` with `1 < s.re` and a prime `p`, the Euler factor
`1 - p ^ (-s)` is nonzero.  Indeed `‖p ^ (-s)‖ = p ^ (-s.re) < 1` since `p ≥ 2`
and `s.re > 1 > 0`. -/
theorem euler_product_term_ne_zero (s : ℂ) (hs : 1 < s.re) (p : ℕ) (hp : p.Prime) :
    (1 : ℂ) - (p : ℂ) ^ (-s) ≠ 0 := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have habs : ‖(p : ℂ) ^ (-s)‖ = (p : ℝ) ^ (-s.re) := by
    have hcast : (p : ℂ) = ((p : ℝ) : ℂ) := by push_cast; ring
    rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos hp0]
    simp
  have hlt : (p : ℝ) ^ (-s.re) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by linarith)
  intro h
  have hone : (p : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp h).symm
  rw [hone, norm_one] at habs
  rw [← habs] at hlt
  exact lt_irrefl _ hlt

end Riemann.zeta

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

