/-
# Huckel C 13
Category: Chemistry
Target: Chem.huckel_C13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` before any module docstring `/-! ... -/`, so the header
-- above is a plain block comment; it is repeated as the module docstring below.)

import Mathlib

/-!
# Huckel C 13
Category: Chemistry
Target: Chem.huckel_C13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Finset

/-- The primitive 13-th root of unity `exp(2πi/13)`. -/

lemma Q_mul_P : Q * P = (13 : ℂ) • (1 : Matrix (ZMod 13) (ZMod 13) ℂ) := by
  ext i j
  rw [Matrix.mul_apply]
  have hstep : ∀ k : ZMod 13, Q i k * P k j = ch (k * (j - i)) := by
    intro k
    simp only [P, Q]
    rw [← ch_add]
    congr 1
    ring
  simp_rw [hstep, sum_ch_mul]
  by_cases h : i = j
  · subst h; simp
  · rw [if_neg (by simpa [sub_eq_zero, eq_comm] using h)]
    simp [Matrix.one_apply_ne h]

