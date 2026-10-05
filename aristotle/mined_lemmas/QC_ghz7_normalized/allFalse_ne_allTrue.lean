import Mathlib

/-!
# Ghz 7 Normalized
Category: Quantum Computing
Target: QC.ghz7_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

/-- The computational basis of a 7-qubit register is indexed by bit strings
`Fin 7 → Bool`; the state space is the complex Hilbert space
`EuclideanSpace ℂ (Fin 7 → Bool)`.

`ghz7` is the 7-qubit GHZ state `(|0000000⟩ + |1111111⟩)/√2`, written as
`(√2)⁻¹ • (e_{all-false} + e_{all-true})` where `e_b = EuclideanSpace.single b 1`
is the computational basis vector `|b⟩`. -/

private lemma allFalse_ne_allTrue : ((fun _ => false) : Fin 7 → Bool) ≠ (fun _ => true) := by
  intro h
  have := congrFun h 0
  simp at this

/-- The un-normalized GHZ vector `|0000000⟩ + |1111111⟩` has norm `√2`. -/
