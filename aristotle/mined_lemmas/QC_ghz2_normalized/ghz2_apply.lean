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

/-- The 2-qubit GHZ state `(|00⟩ + |11⟩)/√2`, as a vector in the 4-dimensional
complex Hilbert space indexed by the computational basis `Fin 2 × Fin 2`. -/

@[simp] lemma ghz2_apply (i : Fin 2 × Fin 2) :
    ghz2 i = if i = (0, 0) then ((Real.sqrt 2)⁻¹ : ℝ) else
      if i = (1, 1) then ((Real.sqrt 2)⁻¹ : ℝ) else 0 := by
  simp only [ghz2, PiLp.smul_apply, PiLp.add_apply, EuclideanSpace.single_apply]
  rcases i with ⟨a, b⟩
  fin_cases a <;> fin_cases b <;> norm_num [Prod.ext_iff]

/-- The 2-qubit GHZ state `(|00⟩ + |11⟩)/√2` is a unit vector. -/
