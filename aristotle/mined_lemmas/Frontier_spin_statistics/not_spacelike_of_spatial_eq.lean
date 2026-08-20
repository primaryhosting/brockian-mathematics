/-
# Spin Statistics
Category: Frontier Physics
Target: Frontier.spin_statistics
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Spin Statistics
Category: Frontier Physics
Target: Frontier.spin_statistics
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped ComplexConjugate
open scoped InnerProductSpace

namespace Frontier

/-! ## Minkowski geometry -/

/-- The Minkowski bilinear form on `ℝ⁴` with signature `(+,-,-,-)`. -/

theorem not_spacelike_of_spatial_eq {x y : Fin 4 → ℝ}
    (h1 : x 1 = y 1) (h2 : x 2 = y 2) (h3 : x 3 = y 3) : ¬ Spacelike x y := by
  simp only [Spacelike, minkowskiForm, Pi.sub_apply, h1, h2, h3, not_lt]
  nlinarith [sq_nonneg (x 0 - y 0)]

/-- The coefficient vectors at spacelike separated points are orthogonal. -/
