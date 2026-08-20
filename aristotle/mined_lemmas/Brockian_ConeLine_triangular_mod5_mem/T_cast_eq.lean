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

lemma T_cast_eq (n : ℕ) : (T n : ZMod 5) = 3 * (n : ZMod 5) * ((n : ZMod 5) + 1) := by
  have h : ((2 * T n : ℕ) : ZMod 5) = ((n * (n + 1) : ℕ) : ZMod 5) := by rw [two_mul_T]
  push_cast at h
  have h6 : (6 : ZMod 5) * (T n : ZMod 5) = 3 * ((n : ZMod 5) * ((n : ZMod 5) + 1)) := by
    rw [show (6 : ZMod 5) * (T n : ZMod 5) = 3 * (2 * (T n : ZMod 5)) by ring, h]
  rw [show (6 : ZMod 5) = 1 by decide, one_mul] at h6
  rw [h6]; ring

/-- Triangular numbers land only on the rays `0, 1, 3` modulo `5`;
rays `2` and `4` carry no triangular number. -/
