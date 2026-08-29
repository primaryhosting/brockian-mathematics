/-
# Goldbach Wheel K 2 947
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_947
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses a plain block comment rather than a `/-! -/` module docstring,
-- because Lean 4 requires `import` commands to precede any doc comment.)

import Mathlib

/-!
# Goldbach Wheel K 2 947
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_947
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

/-- The `K = 2` wheel class condition: a natural number is admissible as a summand in a
`K = 2` Goldbach decomposition modulo the wheel `2 * 3 = 6` exactly when it is coprime to `6`. -/

def WheelK2 (p : ℕ) : Prop := Nat.Coprime p 6

instance (p : ℕ) : Decidable (WheelK2 p) := by unfold WheelK2; infer_instance

/-- Every prime `p ≥ 5` lies in a `K = 2` wheel class, i.e. is coprime to `6`. -/
