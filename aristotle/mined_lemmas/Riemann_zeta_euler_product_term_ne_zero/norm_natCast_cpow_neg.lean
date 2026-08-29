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
