/-
# Triangular Mod 5 Mem
Category: Cone Line
Target: Brockian.ConeLine.triangular_mod5_mem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean 4 requires `import` commands to precede every other command, including
-- module documentation `/-! ... -/`.  The requested header therefore appears above as an
-- ordinary block comment, and verbatim as the module docstring right after the import.

import Mathlib

/-!
# Triangular Mod 5 Mem
Category: Cone Line
Target: Brockian.ConeLine.triangular_mod5_mem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.ConeLine

/-- The `n`-th triangular number, computed in `ℕ` (division performed before casting). -/

lemma two_mul_T (n : ℕ) : 2 * T n = n * (n + 1) :=
  Nat.mul_div_cancel' (Nat.even_mul_succ_self n).two_dvd

/-- In `ZMod 5`, the triangular number `T n` equals `3 * n * (n + 1)`, since `2⁻¹ = 3`. -/
