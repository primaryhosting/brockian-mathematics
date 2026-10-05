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


theorem embed_apply_of_notMem {m n : ℕ} (σ : Fin m → Fin n) (x : EuclideanSpace ℝ (Fin m))
    (j : Fin n) (hj : j ∉ Set.range σ) : (embed σ x) j = 0 := by
  have h : ∀ i, σ i ≠ j := fun i hi => hj ⟨i, hi⟩
  simp [embed, h]

