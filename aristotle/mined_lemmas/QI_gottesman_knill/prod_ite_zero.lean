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

lemma prod_ite_zero {n : ℕ} (P : Fin n → Prop) [DecidablePred P] (f : Fin n → ℂ) :
    (∏ q, if P q then f q else 0) = if ∀ q, P q then ∏ q, f q else 0 := by
  by_cases h : ∀ q, P q
  · rw [if_pos h]
    exact Finset.prod_congr rfl fun q _ => if_pos (h q)
  · rw [if_neg h]
    obtain ⟨q, hq⟩ := not_forall.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ q) (if_neg hq)

