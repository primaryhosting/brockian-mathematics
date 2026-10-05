import Mathlib

/-!
# No Cloning
Category: Quantum Computing
Target: QC.no_cloning
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped InnerProductSpace

namespace QC

/-- The one-qubit state space `ℂ²`, a finite-dimensional complex Hilbert space. -/
abbrev H : Type := EuclideanSpace ℂ (Fin 2)

/-- The two-qubit state space `ℂ² ⊗ ℂ²`, realised as `ℂ^(Fin 2 × Fin 2)`. -/
abbrev HH : Type := EuclideanSpace ℂ (Fin 2 × Fin 2)

/-- The tensor product `x ⊗ y` of two vectors of `H`, viewed inside `HH`. -/

noncomputable def e0 : H := EuclideanSpace.single 0 (1 : ℂ)

/-- A second unit vector, `(3/5)|0⟩ + (4/5)|1⟩`. -/
