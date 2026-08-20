import Mathlib
namespace C3.BSieve4

theorem adm_count_17 (g : ZMod 17) (hg : g ≠ 0) :
    (Finset.univ.filter (fun r : ZMod 17 => r ≠ 0 ∧ r ≠ -g)).card = 15 := by
  revert hg
  revert g
  decide

