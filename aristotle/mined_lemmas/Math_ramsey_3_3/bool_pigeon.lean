/-!
# Ramsey 3 3
Category: Pure Mathematics
Target: Math.ramsey_3_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- This file is self-contained: the proof uses only core `Lean`/`Init` (`Bool`, `Fin`, `decide`),
-- so no `import` is required.  (Mathlib currently has no Ramsey-number API to reuse here.)

namespace Math

/-- Pigeonhole for five booleans: among `b1, …, b5` some three are equal. -/

private theorem bool_pigeon :
    ∀ b1 b2 b3 b4 b5 : Bool,
      (b1 = b2 ∧ b2 = b3) ∨
      (b1 = b2 ∧ b2 = b4) ∨
      (b1 = b2 ∧ b2 = b5) ∨
      (b1 = b3 ∧ b3 = b4) ∨
      (b1 = b3 ∧ b3 = b5) ∨
      (b1 = b4 ∧ b4 = b5) ∨
      (b2 = b3 ∧ b3 = b4) ∨
      (b2 = b3 ∧ b3 = b5) ∨
      (b2 = b4 ∧ b4 = b5) ∨
      (b3 = b4 ∧ b4 = b5) := by decide

/-- If none of `x`, `y`, `z` equals `v`, then all three are equal (they are all `!v`). -/
