/-
# Pell 3
Category: Pure Mathematics
Target: Math.pell_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Pell 3
Category: Pure Mathematics
Target: Math.pell_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **Pell's equation for `d = 3`**: `x² − 3·y² = 1` has a nontrivial integer solution,
i.e. one with `y ≠ 0` (equivalently `x ≠ ±1`).  The fundamental solution is `(x, y) = (2, 1)`. -/

def pellSeq : ℕ → ℤ × ℤ
  | 0 => (2, 1)
  | n + 1 => (2 * (pellSeq n).1 + 3 * (pellSeq n).2, (pellSeq n).1 + 2 * (pellSeq n).2)

