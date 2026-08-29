/-
# Hankel Christoffel 13 18
Category: B Christoffel
Target: Zeta23Scaffold.hankel_christoffel_13_18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Hankel Christoffel 13 18
Category: B Christoffel
Target: Zeta23Scaffold.hankel_christoffel_13_18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace Zeta23Scaffold

/-- The 3×3 rational Hankel (moment) matrix `(m_{i+j})_{0 ≤ i,j ≤ 2}` of the
sine-kernel moment sequence `m_0, …, m_4 = 1, 1, 4/3, 2, 13/4` at `λ = 1`. -/

theorem ladder_assembly : 2 * (1 - christoffelLambda) - 1 = 13 / 18 := by
  rw [one_sub_christoffelLambda]; norm_num

/-- **Main target.** The full statement: the 3×3 sine-kernel Hankel determinant is
`5/108`, the Christoffel function value is `Λ₂(0;1) = 5/36`, hence `1 - Λ = 31/36`
and the ladder assembly gives `2*(1 - Λ) - 1 = 13/18`. -/
