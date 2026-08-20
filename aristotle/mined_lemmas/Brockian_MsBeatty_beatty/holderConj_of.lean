import Mathlib
namespace Brockian.MsBeatty

/-- Hölder conjugacy from the hypotheses `1 < r` and `1/r + 1/s = 1`. -/

private lemma holderConj_of {r s : ℝ} (hr : 1 < r) (hsum : 1 / r + 1 / s = 1) :
    r.HolderConjugate s := by
  rw [Real.holderConjugate_iff]
  exact ⟨hr, by simpa [one_div] using hsum⟩

/-- Membership in the positive Beatty set, expressed with natural-number indices. -/
