import Mathlib
/-!
# Triangular Mod 5 Mem
Category: Cone Line
Target: Brockian.ConeLine.triangular_mod5_mem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- Note: Lean 4 requires `import` lines to precede every other command, including
-- module doc comments, so the requested header block appears immediately after the import.

namespace Brockian.ConeLine

/-- The `n`-th triangular number, computed in `ℕ` (division happens before casting). -/

lemma two_dvd_mul_succ (n : ℕ) : 2 ∣ n * (n + 1) :=
  (Nat.even_mul_succ_self n).two_dvd

/-- Shifting the index by `10` changes the triangular number by a multiple of `5`. -/
