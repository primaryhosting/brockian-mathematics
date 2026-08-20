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

lemma C13_mul_P : C13 * P = P * Matrix.diagonal eig := by
  ext i k
  have hne : i + 1 ≠ i - 1 := by
    intro h
    have h2 : (2 : ZMod 13) = 0 := by linear_combination h
    exact absurd h2 (by decide)
  have hstep : ∀ j : ZMod 13, C13 i j * P j k
      = if j ∈ ({i + 1, i - 1} : Finset (ZMod 13)) then P j k else 0 := by
    intro j
    simp only [C13, Finset.mem_insert, Finset.mem_singleton]
    split <;> simp_all
  rw [Matrix.mul_apply, Matrix.mul_diagonal]
  simp_rw [hstep]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_pair hne]
  simp only [P]
  rw [show (i + 1) * k = i * k + k by ring, show (i - 1) * k = i * k + (-k) by ring,
    ch_add, ch_add, ← mul_add, ch_add_ch_neg]

