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

lemma pellSeq_snd_strictMono : StrictMono fun n => (pellSeq n).2 := by
  refine strictMono_nat_of_lt_succ fun n => ?_
  have := pellSeq_le n
  simp only [pellSeq]
  omega

/-- There are infinitely many integer solutions of `x² − 3y² = 1`. -/
