import Mathlib

/-!
# Ghz 6 Normalized
Category: Quantum Computing
Target: QC.ghz6_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

/-- The computational basis of a 6-qubit register: bit strings of length 6. -/
abbrev Bits6 := Fin 6 → Bool

/-- The all-zeros bit string, labelling the basis vector `|000000⟩`. -/

theorem allZero_ne_allOne : allZero ≠ allOne := by
  intro h
  have := congrFun h 0
  simp [allZero, allOne] at this

/-- The 6-qubit GHZ state `(|000000⟩ + |111111⟩)/√2`, as a vector in the
Hilbert space `ℂ^(2^6)` whose coordinates are indexed by bit strings of length 6. -/
