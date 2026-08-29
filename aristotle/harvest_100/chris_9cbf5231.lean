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

/-- The norm of `(p : ℂ) ^ (-s)` for a positive natural number `p` equals
`(p : ℝ) ^ (-s.re)`. -/
theorem norm_natCast_cpow_neg (p : ℕ) (hp : 0 < p) (s : ℂ) :
    ‖((p : ℂ) ^ (-s))‖ = (p : ℝ) ^ (-s.re) := by
  rw [show ((p : ℂ)) = ((p : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hp)]
  simp

/-- **Euler factor nonvanishing.** For `s : ℂ` with `1 < s.re` and a prime `p`,
the Euler factor `1 - p ^ (-s)` is nonzero. This is a step toward `ζ s ≠ 0`
for `Re s > 1`. -/
theorem euler_product_term_ne_zero {s : ℂ} (hs : 1 < s.re) {p : ℕ} (hp : p.Prime) :
    (1 : ℂ) - (p : ℂ) ^ (-s) ≠ 0 := by
  intro h
  have hpow : ((p : ℂ) ^ (-s)) = 1 := (sub_eq_zero.mp h).symm
  have hnorm : ‖((p : ℂ) ^ (-s))‖ = 1 := by rw [hpow, norm_one]
  have hp2 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hlt : (p : ℝ) ^ (-s.re) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hp2 (by linarith)
  rw [norm_natCast_cpow_neg p hp.pos s] at hnorm
  exact absurd hnorm (ne_of_lt hlt)

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

