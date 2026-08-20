import Mathlib

/-!
# Deutsch Jozsa
Category: Frontier Qi
Target: QI.deutsch_jozsa
Statement: Deutsch–Jozsa decides constant-vs-balanced with one query.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QI

open Finset

/-- The sign `(-1)^b` attached to a boolean. -/

def phase {n : ℕ} (x y : Fin n → Bool) : ℝ := ∏ i, (if x i && y i then (-1 : ℝ) else 1)

/-- The amplitude of the basis state `y` in the final state of the Deutsch–Jozsa
circuit `H^{⊗n} ∘ O_f ∘ H^{⊗n}` applied to `|0…0⟩`, where the oracle `O_f` (used
exactly once) contributes the phase `(-1)^{f x}`. -/
