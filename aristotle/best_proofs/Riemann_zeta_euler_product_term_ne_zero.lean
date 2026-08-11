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

/-- For `s : ℂ` with `1 < s.re` and `p` a prime, the Euler factor `1 - p ^ (-s)` is nonzero.
The proof shows `‖(p : ℂ) ^ (-s)‖ = p ^ (-s.re) < 1`, so `p ^ (-s) ≠ 1`. -/
theorem euler_product_term_ne_zero {s : ℂ} (hs : 1 < s.re) {p : ℕ} (hp : p.Prime) :
    (1 - (p : ℂ) ^ (-s)) ≠ 0 := by
  have hnorm : ‖(p : ℂ) ^ (-s)‖ = (p : ℝ) ^ (-s.re) := by
    rw [Complex.norm_natCast_cpow_of_pos hp.pos]
    simp
  have hlt : ‖(p : ℂ) ^ (-s)‖ < 1 := by
    rw [hnorm]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith)
  intro h
  have h1 : (p : ℂ) ^ (-s) = 1 := by linear_combination -h
  rw [h1] at hlt
  simp at hlt

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

