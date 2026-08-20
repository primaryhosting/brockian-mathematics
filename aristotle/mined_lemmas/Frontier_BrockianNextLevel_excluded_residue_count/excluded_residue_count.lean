import Mathlib
namespace Frontier.BrockianNextLevel

theorem excluded_residue_count (q : ℕ) [NeZero q] (g : ZMod q) (hg : g ≠ 0) :
    (Finset.univ.filter (fun r : ZMod q => r = 0 ∨ r = -g)).card = 2 := by
  have h : (Finset.univ.filter (fun r : ZMod q => r = 0 ∨ r = -g)) = {0, -g} := by
    ext r; simp [Finset.mem_insert]
  rw [h, Finset.card_insert_of_notMem (by simpa using hg), Finset.card_singleton]
