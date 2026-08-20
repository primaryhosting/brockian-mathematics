import Mathlib
namespace Brockian.MsBeatty

/-- Hölder conjugacy from the hypotheses `1 < r` and `1/r + 1/s = 1`. -/

theorem beatty (r s : ℝ) (hr : 1 < r) (hirr : Irrational r) (hsum : 1 / r + 1 / s = 1)
    (n : ℕ) (hn : 0 < n) :
    (∃ m : ℕ, 0 < m ∧ ⌊(m : ℝ) * r⌋ = (n : ℤ)) ↔
      ¬ (∃ m : ℕ, 0 < m ∧ ⌊(m : ℝ) * s⌋ = (n : ℤ)) := by
  have hrs : r.HolderConjugate s := holderConj_of hr hsum
  have key := hirr.beattySeq_symmDiff_beattySeq_pos hrs
  have hmem : ((n : ℤ)) ∈ ({m | 0 < m} : Set ℤ) := by
    simpa using (Int.natCast_pos.2 hn)
  rw [← key, Set.mem_symmDiff, mem_beatty_iff, mem_beatty_iff] at hmem
  exact ⟨fun h ↦ hmem.elim (·.2) (fun x ↦ absurd h x.2),
    fun h ↦ hmem.elim (·.1) (fun x ↦ absurd x.1 h)⟩

end Brockian.MsBeatty

