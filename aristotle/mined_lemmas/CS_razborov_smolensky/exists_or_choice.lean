import Mathlib

/-!
# Binomial estimates

The estimates on binomial coefficients needed for the counting step of the
Razborov–Smolensky theorem.
-/

namespace CS

open Finset

/-- A quantitative form of `centralBinom m ≈ 4 ^ m / √(π m)`. -/

lemma exists_or_choice {m : ℕ} (l : ℕ) (y : Fin m → Cube n → ZMod q) :
    ∃ c : Fin l → Finset (Fin m),
      ((Finset.univ : Finset (Cube n)).filter
        (fun x => orPoly y c x ≠ orTarget y x)).card * 2 ^ l ≤ 2 ^ n := by
  classical
  set Ch := (Finset.univ : Finset (Fin l → Finset (Fin m))) with hCh
  have hChcard : Ch.card = (2 ^ m) ^ l := by
    rw [hCh, Finset.card_univ]
    simp [Fintype.card_finset]
  have hChne : Ch.Nonempty := by
    rw [← Finset.card_pos, hChcard]
    positivity
  have hdouble : ∑ c ∈ Ch, (((Finset.univ : Finset (Cube n)).filter
      (fun x => orPoly y c x ≠ orTarget y x)).card * 2 ^ l) ≤ ∑ _c ∈ Ch, 2 ^ n := by
    have hswap : ∑ c ∈ Ch, ((Finset.univ : Finset (Cube n)).filter
        (fun x => orPoly y c x ≠ orTarget y x)).card
        = ∑ x : Cube n, (Ch.filter (fun c => orPoly y c x ≠ orTarget y x)).card := by
      simp only [Finset.card_filter]
      rw [Finset.sum_comm]
    have hx : ∀ x : Cube n,
        (Ch.filter (fun c => orPoly y c x ≠ orTarget y x)).card * 2 ^ l ≤ (2 ^ m) ^ l := by
      intro x
      have := card_bad_choices (q := q) (l := l) (fun i => y i x)
      refine le_trans (le_of_eq ?_) this
      congr 2
      apply Finset.filter_congr
      intro c _
      rw [orPoly_apply, orTarget]
    calc ∑ c ∈ Ch, (((Finset.univ : Finset (Cube n)).filter
            (fun x => orPoly y c x ≠ orTarget y x)).card * 2 ^ l)
        = (∑ c ∈ Ch, ((Finset.univ : Finset (Cube n)).filter
            (fun x => orPoly y c x ≠ orTarget y x)).card) * 2 ^ l := by
          rw [Finset.sum_mul]
      _ = (∑ x : Cube n, (Ch.filter (fun c => orPoly y c x ≠ orTarget y x)).card) * 2 ^ l := by
          rw [hswap]
      _ = ∑ x : Cube n, ((Ch.filter (fun c => orPoly y c x ≠ orTarget y x)).card * 2 ^ l) := by
          rw [Finset.sum_mul]
      _ ≤ ∑ _x : Cube n, (2 ^ m) ^ l := Finset.sum_le_sum (fun x _ => hx x)
      _ = 2 ^ n * (2 ^ m) ^ l := by
          rw [Finset.sum_const, Finset.card_univ]
          simp
      _ = ∑ _c ∈ Ch, 2 ^ n := by
          rw [Finset.sum_const, hChcard]
          simp [mul_comm]
  obtain ⟨c, _, hc⟩ := Finset.exists_le_of_sum_le hChne hdouble
  exact ⟨c, hc⟩

