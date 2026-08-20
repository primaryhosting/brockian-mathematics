import Mathlib
open Finset
namespace C2.Prob2b

/-- Markov's inequality (counting form): for nonnegative reals `x i`,
`a` times the number of indices with `a ≤ x i` is at most `∑ i, x i`.
The hypothesis `0 < a` turns out to be unnecessary for the proof. -/

theorem variance_nonneg {n : ℕ} (x : Fin n → ℝ) : 0 ≤ (∑ i, (x i)^2)/n - ((∑ i, x i)/n)^2 := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  have hn : (0:ℝ) < n := by exact_mod_cast h
  rw [sub_nonneg, div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
  have := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Fin n))) (f := x)
  simp only [Finset.card_univ, Fintype.card_fin] at this
  nlinarith [this]

end C2.Prob2b

