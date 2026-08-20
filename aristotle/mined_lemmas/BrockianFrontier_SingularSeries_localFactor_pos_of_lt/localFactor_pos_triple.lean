import Mathlib
namespace BrockianFrontier.SingularSeries

/-- Number of residues covered by `G` modulo `p`. -/

theorem localFactor_pos_triple (p : ℕ) : 0 < localFactor ({0, 2, 6} : Finset ℕ) p := by
  refine localFactor_pos_of_lt _ _ (fun hp => ?_)
  have hp2 := hp.two_le
  have hle : nu ({0, 2, 6} : Finset ℕ) p ≤ 3 :=
    le_trans Finset.card_image_le (by decide)
  rcases Nat.lt_or_ge p 4 with hlt | hge
  · interval_cases p <;> decide
  · omega

/-- Every local factor of the admissible quadruple `{0,2,6,8}` is strictly positive. -/
