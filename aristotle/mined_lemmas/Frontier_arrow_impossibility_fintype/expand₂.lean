/-
A Mathlib-facing restatement of `Frontier.arrow_impossibility`, with the finiteness of the
set of voters expressed by `Fintype` instead of by a list of voters covering everything.
-/
import Mathlib
import RequestProject.ArrowImpossibility

namespace Frontier

/-- **Arrow's impossibility theorem** for three alternatives and a finite set of voters:
no social welfare function is unanimous, independent of irrelevant alternatives and
non-dictatorial. -/

theorem expand₂ {F : (V → Ranking) → Ranking} (hU : Unanimous F) (hIIA : IIA F) {S : List V}
    {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hSD : SemiDecisive F S a b) : Decisive F S c b := by
  intro q hq
  -- members of `S` rank `c ≻ a ≻ b`; everybody else puts `a` at the bottom and keeps their
  -- own opinion on `c` versus `b`
  obtain ⟨p, hp⟩ : ∃ p : V → Ranking, p = fun v =>
      if v ∈ S then mkRank c a b (Ne.symm hac) (Ne.symm hbc) hab
      else if (q v).rank c < (q v).rank b then
        mkRank c b a (Ne.symm hbc) (Ne.symm hac) (Ne.symm hab)
      else mkRank b c a hbc (Ne.symm hab) (Ne.symm hac) := ⟨_, rfl⟩
  have hin : ∀ v, v ∈ S → p v = mkRank c a b (Ne.symm hac) (Ne.symm hbc) hab := by
    intro v hv; rw [hp]; simp [hv]
  have hout₁ : ∀ v, v ∉ S → (q v).rank c < (q v).rank b →
      p v = mkRank c b a (Ne.symm hbc) (Ne.symm hac) (Ne.symm hab) := by
    intro v hv h; rw [hp]; simp [hv, h]
  have hout₂ : ∀ v, v ∉ S → ¬ ((q v).rank c < (q v).rank b) →
      p v = mkRank b c a hbc (Ne.symm hab) (Ne.symm hac) := by
    intro v hv h; rw [hp]; simp [hv, h]
  have hab' : prefers (F p) a b := by
    refine hSD p ?_ ?_
    · intro v hv; simp [prefers, hin v hv]
    · intro v hv
      by_cases h : (q v).rank c < (q v).rank b
      · simp [prefers, hout₁ v hv h]
      · simp [prefers, hout₂ v hv h]
  have hca' : prefers (F p) c a := by
    refine hU p c a ?_
    intro v
    by_cases hv : v ∈ S
    · simp [prefers, hin v hv]
    · by_cases h : (q v).rank c < (q v).rank b
      · simp [prefers, hout₁ v hv h]
      · simp [prefers, hout₂ v hv h]
  have hkey : ∀ v, prefers (p v) c b ↔ prefers (q v) c b := by
    intro v
    by_cases hv : v ∈ S
    · exact iff_of_true (by simp [prefers, hin v hv]) (hq v hv)
    · by_cases h : (q v).rank c < (q v).rank b
      · exact iff_of_true (by simp [prefers, hout₁ v hv h]) h
      · exact iff_of_false (by simp [prefers, hout₂ v hv h]) h
  exact (hIIA p q c b hkey).mp (prefers_trans hca' hab')

/-- Field expansion: a coalition semi-decisive for one pair is decisive for every pair. -/
