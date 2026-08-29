import Mathlib
/-!
# Infinite Ramsey
Category: Frontier — Set Theory
Target: Frontier.infinite_ramsey
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open Filter Set


private lemma fin2_eq_one_iff : ∀ x : Fin 2, x = 1 ↔ x ≠ 0 := by decide

/-- For any two-valued function on `ℕ` and any ultrafilter `U`, one of the two fibres
belongs to `U`. -/
