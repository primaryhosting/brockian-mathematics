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

For `s : ℂ` with `1 < s.re` and `p` prime, the Euler factor `1 - p ^ (-s)` is nonzero.
-/

namespace Riemann.zeta

/-- For `s : ℂ` with `1 < s.re` and a prime `p`, the Euler factor `1 - p ^ (-s)` is nonzero.

The proof shows `‖(p : ℂ) ^ (-s)‖ = (p : ℝ) ^ (-s.re) < 1`, so `p ^ (-s) ≠ 1`. -/

theorem euler_product_term_ne_zero (s : ℂ) (hs : 1 < s.re) (p : ℕ) (hp : p.Prime) :
    (1 - (p : ℂ) ^ (-s)) ≠ 0 := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have habs : ‖((p : ℂ) ^ (-s))‖ = (p : ℝ) ^ (-s.re) := by
    rw [show ((p : ℂ)) = ((p : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_cpow_eq_rpow_re_of_pos hp0]
    simp
  have h1 : (p : ℝ) ^ (-s.re) < 1 := by
    apply Real.rpow_lt_one_of_one_lt_of_neg
    · exact_mod_cast hp.one_lt
    · linarith
  intro h
  have h2 : (p : ℂ) ^ (-s) = 1 := by linear_combination -h
  rw [h2] at habs
  simp at habs
  rw [← habs] at h1
  linarith

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

