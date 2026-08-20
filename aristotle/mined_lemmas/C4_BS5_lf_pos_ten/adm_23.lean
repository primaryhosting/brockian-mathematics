import Mathlib
namespace C4.BS5


theorem adm_23 (g : ZMod 23) (hg : g ≠ 0) :
    (Finset.univ.filter (fun r:ZMod 23 => r≠0 ∧ r≠ -g)).card = 21 := by
  revert g; decide

