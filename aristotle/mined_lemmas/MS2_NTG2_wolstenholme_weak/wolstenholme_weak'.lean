import Mathlib
import NTGaps2.ThreeSquares

namespace MS2.NTG2

/-- As stated by the user this theorem has conclusion `True`, so the hypotheses `hp` and `h5`
are not needed. A genuine statement in this direction is `wolstenholme_weak'` below. -/

theorem wolstenholme_weak' (p : ℕ) (hp : p.Prime) : p^2 ∣ Nat.choose (2*p) p - 2 := by
  obtain ⟨m, hm⟩ : ∃ m, p = m + 1 := ⟨p - 1, by have := hp.pos; omega⟩
  have hvan : (2*p).choose p = ∑ k ∈ Finset.range (p+1), p.choose k * p.choose k := by
    rw [two_mul, Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    refine Finset.sum_congr rfl fun k hk => ?_
    simp only [Finset.mem_range] at hk
    rw [Nat.choose_symm (by omega)]
  have hsplit : ∀ f : ℕ → ℕ, ∑ k ∈ Finset.range (m+2), f k
      = (∑ i ∈ Finset.range m, f (i+1)) + (f 0 + f (m+1)) := by
    intro f
    rw [Finset.sum_range_succ, Finset.sum_range_succ' f m]
    ring
  have hdvd : p^2 ∣ ∑ i ∈ Finset.range m, p.choose (i+1) * p.choose (i+1) := by
    refine Finset.dvd_sum fun i hi => ?_
    simp only [Finset.mem_range] at hi
    have h : p ∣ p.choose (i+1) := hp.dvd_choose_self (by omega) (by omega)
    rw [sq]; exact mul_dvd_mul h h
  rw [hvan, show p + 1 = m + 2 by omega, hsplit]
  simp only [Nat.choose_zero_right, ← hm, Nat.choose_self, mul_one]
  simpa using hdvd

