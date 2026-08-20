import Mathlib
namespace BrockianFrontier.SingularSeries

/-- Number of residues covered by `G` modulo `p`. -/

theorem localFactor_pos_of_lt (G : Finset ℕ) (p : ℕ) (h : p.Prime → nu G p < p) :
    0 < localFactor G p := by
  unfold localFactor
  split_ifs with hp
  · have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    apply div_pos
    · rw [sub_pos, div_lt_one hp0]
      exact_mod_cast h hp
    · exact pow_pos (by rw [sub_pos, div_lt_one hp0]; exact_mod_cast hp.one_lt) _
  · norm_num

/-- Every local factor of the admissible prime triple `{0,2,6}` is strictly positive.
    (Extends the verified twin-gap `{0,2}` positivity to k = 3.) -/
