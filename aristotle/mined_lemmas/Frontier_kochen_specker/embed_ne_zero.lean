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


theorem embed_ne_zero {m n : ℕ} (σ : Fin m → Fin n) (hσ : Function.Injective σ)
    {x : EuclideanSpace ℝ (Fin m)} (hx : x ≠ 0) : embed σ x ≠ 0 := by
  intro h
  apply hx
  have h2 := embed_inner σ hσ x x
  rw [h] at h2
  simp at h2
  have hnorm : ‖x‖ = 0 := by nlinarith [norm_nonneg x]
  exact norm_eq_zero.mp hnorm

