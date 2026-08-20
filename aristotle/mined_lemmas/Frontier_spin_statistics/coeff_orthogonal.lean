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

theorem coeff_orthogonal {x y : Fin 4 → ℝ} (h : Spacelike x y) :
    cCoeff x * conj (cCoeff y) + dCoeff x * conj (dCoeff y) = 0 := by
  unfold cCoeff dCoeff
  by_cases hx1 : x 1 = 0 ∧ x 2 = 0 ∧ x 3 = 0 <;>
    by_cases hx2 : x 1 = 1 ∧ x 2 = 0 ∧ x 3 = 0 <;>
    by_cases hy1 : y 1 = 0 ∧ y 2 = 0 ∧ y 3 = 0 <;>
    by_cases hy2 : y 1 = 1 ∧ y 2 = 0 ∧ y 3 = 0 <;>
    simp only [hx1, hx2, hy1, hy2, if_false] <;>
    first
      | (exact absurd h (not_spacelike_of_spatial_eq (by rw [hx1.1, hy1.1])
          (by rw [hx1.2.1, hy1.2.1]) (by rw [hx1.2.2, hy1.2.2])))
      | (exact absurd h (not_spacelike_of_spatial_eq (by rw [hx2.1, hy2.1])
          (by rw [hx2.2.1, hy2.2.1]) (by rw [hx2.2.2, hy2.2.2])))
      | norm_num

