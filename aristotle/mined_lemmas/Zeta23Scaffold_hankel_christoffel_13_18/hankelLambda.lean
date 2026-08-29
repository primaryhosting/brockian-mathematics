/-
# Hankel Christoffel 13 18
Category: B Christoffel
Target: Zeta23Scaffold.hankel_christoffel_13_18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Zeta23Scaffold

/-- The 3×3 rational Hankel (moment) matrix `(m_{i+j})_{0 ≤ i,j ≤ 2}` of the
sine-kernel moment sequence `m_0, …, m_4 = 1, 1, 4/3, 2, 13/4` at `λ = 1`. -/

def hankelLambda : ℚ := hankelM.det / (Matrix.det !![(4:ℚ)/3, 2; 2, 13/4])

/-- The exact-arithmetic core of the conditional `13/18` rung:
(a) `det M = 5/108`; (b) `Λ = 5/36`; (c) `1 - Λ = 31/36`; (d) `2(1 - Λ) - 1 = 13/18`. -/
