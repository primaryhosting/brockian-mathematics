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

theorem cosG : Real.cos (2 * π * 3 * 3 / 4) = 0 := by
  rw [show (2 * π * 3 * 3 / 4 : ℝ) = 2 * π * ((9 : ℕ) : ℝ) / 4 by push_cast; ring, cos_quarter]
  norm_num
  exact cosA

/-! ### The Hückel matrix of `C₄` -/

/-- Adjacency matrix of the cycle graph `C₄` on vertices `0,1,2,3`
(edges `0–1`, `1–2`, `2–3`, `3–0`).  In Hückel theory this matrix (with `α = 0`, `β = 1`)
governs the π-orbital energies of cyclobutadiene. -/
