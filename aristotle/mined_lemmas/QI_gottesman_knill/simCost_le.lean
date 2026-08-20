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

lemma simCost_le {n : ℕ} (gs : List (Gate n)) : simCost gs ≤ 6 * n * gs.length := by
  have h : (gs.map gateCost).sum ≤ 3 * gs.length := by
    induction gs with
    | nil => simp
    | cons g gs ih =>
        have hg : gateCost g ≤ 3 := by cases g <;> simp [gateCost]
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        omega
  calc simCost gs = 2 * n * (gs.map gateCost).sum := rfl
    _ ≤ 2 * n * (3 * gs.length) := by exact Nat.mul_le_mul_left _ h
    _ = 6 * n * gs.length := by ring

