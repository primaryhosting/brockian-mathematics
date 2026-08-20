/-
# Huckel C 4
Category: Chemistry
Target: Chem.huckel_C4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` commands to precede any module doc comment `/-! ... -/`,
-- so the header above is a plain block comment and is repeated as a doc comment below.)

import Mathlib

/-!
# Huckel C 4
Category: Chemistry
Target: Chem.huckel_C4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real

namespace Chem

/-! ### Values of `cos (2πm/4)` -/

/-- `cos (2πm/4)` only depends on `m % 4`. -/

theorem huckel_C4_eigenvector (k : Fin 4) :
    v4 k ≠ 0 ∧ A4.mulVec (v4 k) = (2 * Real.cos (2 * π * (k : ℕ) / 4)) • v4 k := by
  have h0 : v4 k 0 = 1 := by simp [v4]
  refine ⟨fun h => ?_, ?_⟩
  · rw [h] at h0; simp at h0
  · fin_cases k
    exacts [eig_zero, eig_one, eig_two, eig_three]

/-- **Hückel theory for cyclobutadiene (C₄).**  The adjacency eigenvalues of the cycle graph
`C₄` are exactly `2 cos (2πk/4)` for `k = 0,1,2,3`: the characteristic polynomial factors
accordingly, and each of these values carries an explicit nonzero eigenvector. -/
