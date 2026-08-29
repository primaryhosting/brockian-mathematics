/-
# Ghz 8 Normalized
Category: Quantum Computing
Target: QC.ghz8_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

/-- The 8-qubit GHZ state `(|0…0⟩ + |1…1⟩)/√2`, as a vector in the Hilbert space
`EuclideanSpace ℂ (Fin 8 → Bool)`, whose index type `Fin 8 → Bool` enumerates the
`2^8` computational basis states. -/

theorem ghz8_eq_smul_add_single :
    ghz8 = (((1 / Real.sqrt 2 : ℝ) : ℂ)) •
      (EuclideanSpace.single (fun _ => false) (1 : ℂ)
        + EuclideanSpace.single (fun _ => true) (1 : ℂ)) := by
  have hab : (fun _ => false : Fin 8 → Bool) ≠ (fun _ => true) := by
    intro h
    have := congrFun h 0
    simp at this
  ext v
  by_cases h1 : v = (fun _ => false)
  · subst h1; simp [ghz8, EuclideanSpace.single_apply, hab]
  · by_cases h2 : v = (fun _ => true) <;>
      simp [ghz8, EuclideanSpace.single_apply, h1, h2, Ne.symm hab]

/-- The 8-qubit GHZ state is a unit vector. -/
