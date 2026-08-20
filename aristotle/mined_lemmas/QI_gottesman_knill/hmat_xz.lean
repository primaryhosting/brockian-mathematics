/-
# Gottesman Knill
Category: Frontier Qi
Target: QI.gottesman_knill
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` lines to precede any module docstring `/-! ... -/`,
-- so the header above is a plain comment and is repeated as a docstring below.)

import Mathlib

/-!
# Gottesman Knill
Category: Frontier Qi
Target: QI.gottesman_knill
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Matrix

namespace QI

/-! ## Phases and signs -/

/-- Computational basis labels for `n` qubits: bit strings of length `n`. -/
abbrev Bits (n : ℕ) : Type := Fin n → ZMod 2

/-- The fourth root of unity `i ^ s` attached to `s : ZMod 4`. -/

lemma hmat_xz (x z : ZMod 2) : hmat * xz x z = psign (x * z) • (xz z x * hmat) := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.smul_apply, hmat, xz, smul_eq_mul, sum_zmod2]
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;>
    rcases zmod2_cases x with rfl | rfl <;> rcases zmod2_cases z with rfl | rfl <;>
    simp [psign]

/-- `S (X^x Z^z) = i^x (X^x Z^(x+z)) S`. -/
