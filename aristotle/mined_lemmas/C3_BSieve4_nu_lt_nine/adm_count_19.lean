import Mathlib
namespace C3.BSieve4

theorem adm_count_19 (g : ZMod 19) (hg : g ≠ 0) :
    (Finset.univ.filter (fun r : ZMod 19 => r ≠ 0 ∧ r ≠ -g)).card = 17 := by
  revert hg
  revert g
  decide

end C3.BSieve4

