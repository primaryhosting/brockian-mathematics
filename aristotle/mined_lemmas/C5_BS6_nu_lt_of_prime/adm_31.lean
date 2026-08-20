import Mathlib
namespace C5.BS6

theorem adm_31 (g : ZMod 31) (hg : g ≠ 0) :
    (Finset.univ.filter (fun r : ZMod 31 => r ≠ 0 ∧ r ≠ -g)).card = 29 := by
  revert g
  decide

end C5.BS6

