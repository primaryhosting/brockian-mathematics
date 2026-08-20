import Mathlib
namespace C5.BS6

theorem adm_29 (g : ZMod 29) (hg : g ≠ 0) :
    (Finset.univ.filter (fun r : ZMod 29 => r ≠ 0 ∧ r ≠ -g)).card = 27 := by
  revert g
  decide

