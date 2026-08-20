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

theorem v4_three : v4 3 = ![1, 0, -1, 0] := by
  funext j; fin_cases j <;> simp [v4, cosC, cosF, cosG]

/-! ### The spectrum -/

/-- The characteristic polynomial of the `C₄` adjacency matrix, evaluated at any real `μ`,
factors as `∏ k, (μ - 2 cos (2πk/4))`. -/
