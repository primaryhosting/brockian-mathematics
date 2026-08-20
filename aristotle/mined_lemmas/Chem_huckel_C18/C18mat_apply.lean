/-
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Matrix Polynomial Finset

noncomputable section

/-- A primitive 18-th root of unity. -/

theorem C18mat_apply (i j : ZMod 18) :
    C18mat i j = if j = i - 1 ∨ j = i + 1 then 1 else 0 := by
  have e1 : (i - j = 1) ↔ j = i - 1 :=
    ⟨fun h => by linear_combination -h, fun h => by linear_combination -h⟩
  have e2 : (i - j = -1) ↔ j = i + 1 :=
    ⟨fun h => by linear_combination -h, fun h => by linear_combination -h⟩
  simp only [C18mat, Matrix.circulant_apply, e1, e2]

/-- The adjacency matrix is symmetric. -/
