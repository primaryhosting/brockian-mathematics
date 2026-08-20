import Mathlib
import RequestProject.ErdosDiscrepancy
import RequestProject.ErdosDiscrepancyMathlib
import RequestProject.ErdosDiscrepancySpecialCases
import RequestProject.ErdosDiscrepancyMeasure

/-!
# The base case for completely multiplicative sequences

For a completely multiplicative `±1` sequence every homogeneous sum is `f d` times an
ordinary partial sum, so only the sums `S n = f 1 + ⋯ + f n` matter.  Tracking the four
values `f 2, f 3, f 5, f 7` shows that one of `S 4, S 6, S 8, S 10` must exceed `1` in
absolute value: for completely multiplicative sequences the length `10` already forces
discrepancy `2` (as opposed to `12` in general).
-/

namespace Frontier

/-- Unfolding the ordinary partial sums. -/

theorem exists_of_lt_discrepancyUpTo {f : ℕ → ℤ} {C N : ℕ} (h : C < discrepancyUpTo f N) :
    ∃ d n : ℕ, 1 ≤ d ∧ 1 ≤ n ∧ n * d ≤ N ∧ C < (homogSum f d n).natAbs := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [discrepancyUpTo] at h
  have hne : ((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)).Nonempty :=
    ⟨(1, 1), by simp [Finset.mem_product]; omega⟩
  obtain ⟨p, hp, hval⟩ := Finset.exists_mem_eq_sup _ hne
    (fun p : ℕ × ℕ => if p.1 * p.2 ≤ N then (homogSum f p.2 p.1).natAbs else 0)
  rw [discrepancyUpTo, hval] at h
  by_cases hle : p.1 * p.2 ≤ N
  · rw [if_pos hle] at h
    simp only [Finset.mem_product, Finset.mem_Icc] at hp
    exact ⟨p.2, p.1, hp.2.1, hp.1.1, hle, h⟩
  · rw [if_neg hle] at h
    omega

/-- The Erdős discrepancy statement, in terms of the discrepancy function. -/
