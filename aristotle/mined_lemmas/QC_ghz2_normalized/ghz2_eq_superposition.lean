/-
# Ghz 2 Normalized
Category: Quantum Computing
Target: QC.ghz2_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Ghz 2 Normalized
Category: Quantum Computing
Target: QC.ghz2_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

/-- The 2-qubit GHZ state `(|00⟩ + |11⟩)/√2`, as a vector in the Hilbert space
`EuclideanSpace ℂ (Fin 2 × Fin 2)` indexed by pairs of qubit values. -/

theorem ghz2_eq_superposition : ghz2 = ((Real.sqrt 2 : ℂ))⁻¹ •
    (EuclideanSpace.single ((0 : Fin 2), (0 : Fin 2)) (1 : ℂ)
      + EuclideanSpace.single ((1 : Fin 2), (1 : Fin 2)) (1 : ℂ)) := by
  ext p
  by_cases h0 : p = (0, 0)
  · simp [ghz2, h0, EuclideanSpace.single_apply, Prod.ext_iff]
  · by_cases h1 : p = (1, 1)
    · simp [ghz2, h1, EuclideanSpace.single_apply, Prod.ext_iff]
    · simp only [ghz2, h0, h1, or_self, WithLp.ofLp_toLp, PiLp.smul_apply,
        PiLp.add_apply, EuclideanSpace.single_apply, smul_eq_mul]
      rcases p with ⟨i, j⟩
      fin_cases i <;> fin_cases j <;> simp_all [Prod.ext_iff]

/-- The 2-qubit GHZ state is a unit vector. -/
