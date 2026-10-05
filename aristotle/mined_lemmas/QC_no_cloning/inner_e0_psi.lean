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

lemma inner_e0_psi : ⟪e0, psi⟫_ℂ = 3 / 5 := by
  simp [e0, psi, PiLp.inner_apply, RCLike.inner_apply, EuclideanSpace.single_apply]

