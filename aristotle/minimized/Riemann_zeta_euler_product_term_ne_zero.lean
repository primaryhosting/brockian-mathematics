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

namespace Riemann.zeta

/-- For `s : ℂ` with `1 < s.re` and `p` a prime, the Euler factor
`1 - (p : ℂ) ^ (-s)` is nonzero.

The proof shows `‖(p : ℂ) ^ (-s)‖ = (p : ℝ) ^ (-s.re) < 1`, using
`Complex.norm_cpow_eq_rpow_re_of_pos` and `Real.rpow_lt_one_of_one_lt_of_neg`. -/
theorem euler_product_term_ne_zero
    {s : ℂ} (hs : 1 < s.re) {p : ℕ} (hp : Nat.Prime p) :
    (1 - (p : ℂ) ^ (-s)) ≠ 0 := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hcast : ((p : ℂ)) = ((p : ℝ) : ℂ) := by push_cast; ring
  have habs : ‖((p : ℂ)) ^ (-s)‖ = (p : ℝ) ^ (-s.re) := by
    rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos hp0]
    simp
  have hlt : ‖((p : ℂ)) ^ (-s)‖ < 1 := by
    rw [habs]
    apply Real.rpow_lt_one_of_one_lt_of_neg
    · exact_mod_cast hp.one_lt
    · linarith
  intro h
  have h1 : ((p : ℂ)) ^ (-s) = 1 := by linear_combination -h
  rw [h1] at hlt
  simp at hlt

end Riemann.zeta

