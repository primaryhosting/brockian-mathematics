/-
# No Cloning
Category: Quantum Computing
Target: QC.no_cloning
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# No Cloning
Category: Quantum Computing
Target: QC.no_cloning
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

/-- A single qubit: the two-dimensional complex Hilbert space `ℂ²`. -/
abbrev Qubit : Type := EuclideanSpace ℂ (Fin 2)

/-- The tensor square `Qubit ⊗ Qubit`, realized as `ℂ^(Fin 2 × Fin 2)`. -/
abbrev Pair : Type := EuclideanSpace ℂ (Fin 2 × Fin 2)

/-- The tensor product `|ψ⟩ ⊗ |φ⟩` of two qubit states. -/

noncomputable def zeroState : Qubit := EuclideanSpace.single 0 1

/-- **No-cloning theorem.** There is no unitary `U` on `H ⊗ H` (here `H = ℂ²`) with
`U (|ψ⟩ ⊗ |0⟩) = |ψ⟩ ⊗ |ψ⟩` for every state (unit vector) `|ψ⟩`. -/
