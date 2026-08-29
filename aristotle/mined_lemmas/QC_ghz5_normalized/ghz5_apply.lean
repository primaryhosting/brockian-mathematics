import Mathlib

/-!
# Ghz 5 Normalized
Category: Quantum Computing
Target: QC.ghz5_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open Finset

/-- The 5-qubit GHZ state `(|00000⟩ + |11111⟩)/√2`, as a vector in the Hilbert space
`EuclideanSpace ℂ (Fin 5 → Bool)` whose basis vectors `EuclideanSpace.single b 1` are the
computational basis states `|b⟩` indexed by bit strings `b : Fin 5 → Bool`. -/

lemma ghz5_apply (b : Fin 5 → Bool) :
    ghz5 b = if b = (fun _ => false) ∨ b = (fun _ => true) then ((Real.sqrt 2)⁻¹ : ℂ) else 0 := by
  by_cases h1 : b = (fun _ => false)
  · subst h1
    simp only [ghz5, EuclideanSpace.single_apply, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
    norm_num
    decide
  · by_cases h2 : b = (fun _ => true)
    · subst h2
      simp only [ghz5, EuclideanSpace.single_apply, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
      norm_num
      decide
    · simp [ghz5, EuclideanSpace.single_apply, h1, h2]

/-- **The 5-qubit GHZ state is a unit vector.** -/
