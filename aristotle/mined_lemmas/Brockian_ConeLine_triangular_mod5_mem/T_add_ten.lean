import Mathlib

/-!
# Triangular Mod 5 Mem
Category: Cone Line
Target: Brockian.ConeLine.triangular_mod5_mem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace Brockian.ConeLine

/-- The `n`-th triangular number, as a natural number (exact division by `2`). -/

lemma T_add_ten (n : ℕ) : T (n + 10) = T n + (10 * n + 55) := by
  have h1 := two_mul_T n
  have h2 := two_mul_T (n + 10)
  nlinarith [h1, h2]

