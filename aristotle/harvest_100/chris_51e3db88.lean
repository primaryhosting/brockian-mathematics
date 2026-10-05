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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Riemann.zeta

/-- The norm of the Euler factor's subtracted term is `p ^ (-s.re)`, which is `< 1`
when `p` is a prime and `1 < s.re`. -/
theorem norm_prime_cpow_neg_lt_one {s : ℂ} (hs : 1 < s.re) {p : ℕ} (hp : Nat.Prime p) :
    ‖(p : ℂ) ^ (-s)‖ < 1 := by
  have hp1 : 1 < p := hp.one_lt
  have hnorm : ‖(p : ℂ) ^ (-s)‖ = (p : ℝ) ^ (-s.re) := by
    rw [Complex.norm_natCast_cpow_of_pos (by omega)]
    simp
  rw [hnorm]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp1) (by linarith)

/-- For `s : ℂ` with `1 < s.re` and `p` prime, the Euler factor `1 - p ^ (-s)` is nonzero. -/
theorem euler_product_term_ne_zero {s : ℂ} (hs : 1 < s.re) {p : ℕ} (hp : Nat.Prime p) :
    (1 : ℂ) - (p : ℂ) ^ (-s) ≠ 0 := by
  intro h
  have hone : (p : ℂ) ^ (-s) = 1 := by linear_combination -h
  have := norm_prime_cpow_neg_lt_one hs hp
  rw [hone] at this
  simp at this

end Riemann.zeta

