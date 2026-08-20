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

theorem expand₁ {F : (V → Ranking) → Ranking} (hU : Unanimous F) (hIIA : IIA F) {S : List V}
    {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hSD : SemiDecisive F S a b) : Decisive F S a c := by
  intro q hq
  -- members of `S` rank `a ≻ b ≻ c`; everybody else puts `b` on top and keeps their
  -- own opinion on `a` versus `c`
  obtain ⟨p, hp⟩ : ∃ p : V → Ranking, p = fun v =>
      if v ∈ S then mkRank a b c hab hac hbc
      else if (q v).rank a < (q v).rank c then mkRank b a c (Ne.symm hab) hbc hac
      else mkRank b c a hbc (Ne.symm hab) (Ne.symm hac) := ⟨_, rfl⟩
  have hin : ∀ v, v ∈ S → p v = mkRank a b c hab hac hbc := by
    intro v hv; rw [hp]; simp [hv]
  have hout₁ : ∀ v, v ∉ S → (q v).rank a < (q v).rank c →
      p v = mkRank b a c (Ne.symm hab) hbc hac := by
    intro v hv h; rw [hp]; simp [hv, h]
  have hout₂ : ∀ v, v ∉ S → ¬ ((q v).rank a < (q v).rank c) →
      p v = mkRank b c a hbc (Ne.symm hab) (Ne.symm hac) := by
    intro v hv h; rw [hp]; simp [hv, h]
  -- society prefers `a` to `b`, since `S` is semi-decisive for that pair
  have hab' : prefers (F p) a b := by
    refine hSD p ?_ ?_
    · intro v hv; simp [prefers, hin v hv]
    · intro v hv
      by_cases h : (q v).rank a < (q v).rank c
      · simp [prefers, hout₁ v hv h]
      · simp [prefers, hout₂ v hv h]
  -- everybody prefers `b` to `c`, so society does too
  have hbc' : prefers (F p) b c := by
    refine hU p b c ?_
    intro v
    by_cases hv : v ∈ S
    · simp [prefers, hin v hv]
    · by_cases h : (q v).rank a < (q v).rank c
      · simp [prefers, hout₁ v hv h]
      · simp [prefers, hout₂ v hv h]
  -- `p` and `q` agree on `a` versus `c`
  have hkey : ∀ v, prefers (p v) a c ↔ prefers (q v) a c := by
    intro v
    by_cases hv : v ∈ S
    · exact iff_of_true (by simp [prefers, hin v hv]) (hq v hv)
    · by_cases h : (q v).rank a < (q v).rank c
      · exact iff_of_true (by simp [prefers, hout₁ v hv h]) h
      · exact iff_of_false (by simp [prefers, hout₂ v hv h]) h
  exact (hIIA p q a c hkey).mp (prefers_trans hab' hbc')

/-- Field expansion, second half: a coalition semi-decisive for `(a,b)` is decisive for `(c,b)`. -/
