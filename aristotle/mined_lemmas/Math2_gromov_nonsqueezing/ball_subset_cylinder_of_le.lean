/-
# Gromov Nonsqueezing
Category: Frontier Math
Target: Math2.gromov_nonsqueezing
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Gromov Nonsqueezing
Category: Frontier Math
Target: Math2.gromov_nonsqueezing
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace Math2

/-- The standard symplectic form on `ℝ^{2n}`, with coordinates indexed by
`Fin n × Fin 2` (the pair `(i, 0)`, `(i, 1)` being the `i`-th conjugate pair). -/

theorem ball_subset_cylinder_of_le {n : ℕ} {r R : ℝ} (h : r ≤ R) (hr : 0 ≤ r) :
    (LinearMap.id (R := ℝ) (M := (Fin (n + 1) × Fin 2 → ℝ))) '' ball r ⊆ cylinder R := by
  rintro w ⟨v, hv, rfl⟩
  have hle : (v (0, 0)) ^ 2 + (v (0, 1)) ^ 2 ≤ sqNorm v := by
    rw [sqNorm_eq]
    exact Finset.single_le_sum
      (f := fun i : Fin (n + 1) => (v (i, 0)) ^ 2 + (v (i, 1)) ^ 2)
      (fun i _ => by positivity) (Finset.mem_univ 0)
  have hlt : sqNorm v < r ^ 2 := hv
  have : r ^ 2 ≤ R ^ 2 := by nlinarith
  exact lt_of_le_of_lt hle (by simpa using lt_of_lt_of_le hlt this)

end Math2

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

