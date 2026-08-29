/-
# Ghz 6 Normalized
Category: Quantum Computing
Target: QC.ghz6_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Ghz 6 Normalized
Category: Quantum Computing
Target: QC.ghz6_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean 4 requires `import` commands to precede every other command, including
-- module docstrings (`/-! ... -/`).  The header therefore appears twice: as a plain
-- block comment at the very top of the file, and as the module docstring below the
-- import.  The text is otherwise identical.

namespace QC

/-- The all-zeros basis label `|000000⟩` of a 6-qubit register. -/

theorem ghz6_eq_smul_add_single :
    ghz6 = ((1 / Real.sqrt 2 : ℝ) : ℂ) •
      (EuclideanSpace.single allZeros (1 : ℂ) + EuclideanSpace.single allOnes (1 : ℂ)) := by
  have hne := allZeros_ne_allOnes
  ext x
  simp only [ghz6, WithLp.ofLp_toLp, PiLp.smul_apply, PiLp.add_apply,
    EuclideanSpace.single_apply, smul_eq_mul]
  by_cases h0 : x = allZeros
  · subst h0; simp [hne]
  · by_cases h1 : x = allOnes
    · subst h1; simp [hne.symm]
    · simp [h0, h1]

/-- The 6-qubit GHZ state `(|0…0⟩ + |1…1⟩)/√2` is a unit vector. -/
