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

lemma inner_tens (x y z w : H) :
    ⟪tens x y, tens z w⟫_ℂ = ⟪x, z⟫_ℂ * ⟪y, w⟫_ℂ := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, tens_apply, Fintype.sum_prod_type,
    map_mul, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- The "blank" state `|0⟩`. -/
