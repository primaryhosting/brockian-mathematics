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


theorem kochen_specker_of_four_le (n : ℕ) (hn : 4 ≤ n) :
    ¬ ∃ f : EuclideanSpace ℝ (Fin n) → Bool,
        ∀ v : Fin n → EuclideanSpace ℝ (Fin n),
          (∀ i, v i ≠ 0) →
          (∀ i j, i ≠ j → inner ℝ (v i) (v j) = (0 : ℝ)) →
          (∑ i, if f (v i) then (1 : ℕ) else 0) = 1 :=
  kochen_specker_of_le (by norm_num) hn kochen_specker_dim_four

end Frontier

