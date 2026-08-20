import Mathlib

/-!
# Bell Orthonormal
Category: Quantum Computing
Target: QC.bell_orthonormal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open scoped ComplexConjugate

/-- The two-qubit state space `ℂ² ⊗ ℂ²`, realized as the Hilbert space of
functions `Fin 2 × Fin 2 → ℂ` with the standard inner product. -/
abbrev Qubit2 := EuclideanSpace ℂ (Fin 2 × Fin 2)

/-- `1/√2`, the normalization constant of the Bell states. -/

noncomputable def bellMatrix : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![ !![invSqrt2, 0; 0, invSqrt2],
     !![invSqrt2, 0; 0, -invSqrt2],
     !![0, invSqrt2; invSqrt2, 0],
     !![0, invSqrt2; -invSqrt2, 0] ]

/-- The four Bell states
`(|00⟩ ± |11⟩)/√2` and `(|01⟩ ± |10⟩)/√2` as vectors of `ℂ² ⊗ ℂ²`. -/
