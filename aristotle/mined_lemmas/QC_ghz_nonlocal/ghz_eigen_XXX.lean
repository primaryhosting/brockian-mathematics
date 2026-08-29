/- (Lean requires `import` to precede any module docstring, so this required header is
   reproduced verbatim as a plain block comment.)
/-!
# Ghz Nonlocal
Category: Quantum Computing
Target: QC.ghz_nonlocal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/

import Mathlib

namespace QC

/-- Index type for the computational basis of three qubits. -/
abbrev Q3 := Fin 2 × Fin 2 × Fin 2

/-- The Pauli `X` matrix. -/

lemma ghz_eigen_XXX : Matrix.mulVec (op3 pauliX pauliX pauliX) ghz = ghz := by
  funext p
  obtain ⟨a, b, c⟩ := p
  rw [mulVec_ghz]
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp [op3, ghz, pauliX]

/-- **Mermin's argument.** No local hidden-variable model, i.e. no pre-assignment of
deterministic outcomes `x i, y i ∈ {-1, 1}` to the local measurements `X` and `Y` on
each of the three qubits, can reproduce the four GHZ correlations
`XYY = YXY = YYX = -1` and `XXX = +1`: multiplying the first three equations gives
`x 0 * x 1 * x 2 = -1` (each `y i` occurring twice, squaring to `1`), contradicting the
fourth.  (Only the `±1`-valuedness of the `Y`-outcomes `y` is needed for the argument,
so no hypothesis on `x` is imposed.) -/
