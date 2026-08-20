/-
# Ghz 5 Normalized
Category: Quantum Computing
Target: QC.ghz5_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Ghz 5 Normalized
Category: Quantum Computing
Target: QC.ghz5_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

/-- The 5-qubit GHZ state `(|00000⟩ + |11111⟩)/√2`, as a vector in the Hilbert space
`EuclideanSpace ℂ (Fin 5 → Fin 2)` of amplitudes indexed by 5-bit strings. -/

theorem ghz5_eq_smul_add_single : ghz5 = ((Real.sqrt 2 : ℝ)⁻¹ : ℂ) •
    (EuclideanSpace.single (fun _ => (0 : Fin 2)) (1 : ℂ)
      + EuclideanSpace.single (fun _ => (1 : Fin 2)) (1 : ℂ)) := by
  ext b
  by_cases hp : ∀ i, b i = 0 <;> by_cases hq : ∀ i, b i = 1 <;>
    simp [ghz5, EuclideanSpace.single_apply, funext_iff, eq_comm, one_div, hp, hq]

/-- The 5-qubit GHZ state is a unit vector. -/
