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


theorem embed_inner {m n : ℕ} (σ : Fin m → Fin n) (hσ : Function.Injective σ)
    (x y : EuclideanSpace ℝ (Fin m)) : inner ℝ (embed σ x) (embed σ y) = inner ℝ x y := by
  simp [embed, inner_sum, sum_inner, hσ.eq_iff, PiLp.inner_apply, mul_comm]

