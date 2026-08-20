import Mathlib
namespace C2.BSieve3

theorem admissible_count_thirteen (g : ZMod 13) (hg : g ≠ 0) :
    (Finset.univ.filter (fun r : ZMod 13 => r ≠ 0 ∧ r ≠ -g)).card = 11 := by
  revert g; decide

end C2.BSieve3

