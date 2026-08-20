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

lemma tp_one {n : ℕ} : tp (fun _ : Fin n => (1 : Matrix (ZMod 2) (ZMod 2) ℂ)) = 1 := by
  ext a b
  by_cases h : a = b
  · subst h; simp [tp]
  · simp only [tp, Matrix.one_apply, if_neg h]
    obtain ⟨q, hq⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ q) (by simp [Matrix.one_apply, hq])

