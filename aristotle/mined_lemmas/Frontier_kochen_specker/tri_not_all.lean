import Mathlib

/-!
# The rays of a three dimensional Kochen–Specker configuration

The 33 rays of a Kochen–Specker configuration in `ℝ³` (coordinates in `{0, ±1, ±√2}`),
together with the auxiliary vectors completing each orthogonal pair to a frame, and the
boolean bookkeeping lemmas used in the case analysis.
-/

set_option maxHeartbeats 4000000
set_option autoImplicit false

namespace Frontier
namespace KS3

/-- The three dimensional real Hilbert space. -/
abbrev V3 := EuclideanSpace ℝ (Fin 3)


theorem tri_not_all (h : (if x then 1 else 0) + (if y then 1 else 0) + (if z then 1 else 0) = (1 : ℕ))
    (hx : x = false) (hy : y = false) (hz : z = false) : False := by
  cases x <;> cases y <;> cases z <;> simp_all

end KS3

end Frontier

import RequestProject.KS3Vectors

/-!
# Kochen–Specker in dimension three

The case analysis refuting the existence of a `{0,1}`-valuation on `ℝ³`.
-/

set_option maxHeartbeats 4000000
set_option autoImplicit false

namespace Frontier
/--
**Kochen–Specker theorem in dimension three.**

There is no `{0,1}`-valued (noncontextual) assignment on the vectors of `ℝ³` assigning
the value `1` to exactly one vector of each orthogonal frame.  The proof exhibits a
33-ray configuration with coordinates in `{0, ±1, ±√2}` and refutes every valuation by
case analysis.
-/
