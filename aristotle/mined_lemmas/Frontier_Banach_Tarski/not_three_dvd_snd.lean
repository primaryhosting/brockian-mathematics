import RequestProject.BT.Ball

/-!
# Banach Tarski
Category: Frontier — Set Theory
Target: Frontier.Banach_Tarski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Metric Set
open scoped Pointwise

namespace Frontier

/-- The vector by which the second copy of the ball is translated. -/

theorem not_three_dvd_snd : ∀ (L : List (Fin 2 × Bool)), FreeGroup.IsReduced L → L ≠ [] →
    ¬ ((3 : ℤ) ∣ (evalW L).2.1) := by
  intro L
  induction L with
  | nil => intro _ h; exact absurd rfl h
  | cons x L' ih =>
    intro hred _
    cases L' with
    | nil =>
      rcases fin2_eq_zero_or_one x.1 with hx | hx
      · simp only [evalW_cons, evalW_nil, stp, if_pos hx]
        cases hb : x.2 <;> simp [sgnZ]
      · simp only [evalW_cons, evalW_nil, stp, if_neg (by rw [hx]; decide : ¬ x.1 = 0)]
        cases hb : x.2 <;> simp [sgnZ]
    | cons y t =>
      have hred2 := FreeGroup.isReduced_cons_cons.1 hred
      have hsame : x.1 = y.1 → x.2 = y.2 := hred2.1
      have hB' : ¬ ((3:ℤ) ∣ (evalW (y :: t)).2.1) := ih hred2.2 (by simp)
      have hx1 : ¬ x.1 = 0 ↔ x.1 = 1 := by
        constructor
        · intro h; rcases fin2_eq_zero_or_one x.1 with h' | h'
          · exact absurd h' h
          · exact h'
        · intro h; rw [h]; decide
      have hy1 : ¬ y.1 = 0 ↔ y.1 = 1 := by
        constructor
        · intro h; rcases fin2_eq_zero_or_one y.1 with h' | h'
          · exact absurd h' h
          · exact h'
        · intro h; rw [h]; decide
      rcases fin2_eq_zero_or_one x.1 with hx | hx <;>
        rcases fin2_eq_zero_or_one y.1 with hy | hy
      · have hb : x.2 = y.2 := hsame (hx.trans hy.symm)
        simp only [evalW_cons, stp, if_pos hx, if_pos hy, hb] at hB' ⊢
        cases hy2 : y.2 <;> norm_num [sgnZ, hy2] at hB' ⊢ <;> omega
      · simp only [evalW_cons, stp, if_pos hx, if_neg (hy1.2 hy)] at hB' ⊢
        cases hx2 : x.2 <;> cases hy2 : y.2 <;>
          norm_num [sgnZ, hx2, hy2] at hB' ⊢ <;> omega
      · simp only [evalW_cons, stp, if_neg (hx1.2 hx), if_pos hy] at hB' ⊢
        cases hx2 : x.2 <;> cases hy2 : y.2 <;>
          norm_num [sgnZ, hx2, hy2] at hB' ⊢ <;> omega
      · have hb : x.2 = y.2 := hsame (hx.trans hy.symm)
        simp only [evalW_cons, stp, if_neg (hx1.2 hx), if_neg (hy1.2 hy), hb] at hB' ⊢
        cases hy2 : y.2 <;> norm_num [sgnZ, hy2] at hB' ⊢ <;> omega

/-! ### The analytic side -/

/-- The image of a letter under the representation. -/
