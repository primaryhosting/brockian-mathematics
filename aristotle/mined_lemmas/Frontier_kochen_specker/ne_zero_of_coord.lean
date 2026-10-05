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


theorem ne_zero_of_coord {v : KSSpace} (i : Fin 4) (h : v i ≠ 0) : v ≠ 0 := by
  intro hv
  apply h
  simp [hv]

/-! ### The 18 vectors of the Cabello–Estebaranz–García-Alcaine set -/

