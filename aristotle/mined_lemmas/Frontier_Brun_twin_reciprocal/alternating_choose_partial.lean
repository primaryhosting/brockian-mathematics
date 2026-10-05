import RequestProject.Defs

/-!
# The Bonferroni / Brun truncation inequality

Truncating the inclusion–exclusion sum at an even level `t` gives an upper bound for the
sifted count.
-/

namespace Brun

open Finset

/-- Partial alternating sums of binomial coefficients. -/

lemma alternating_choose_partial (s t : ℕ) :
    ∑ j ∈ range (t + 1), (-1 : ℝ) ^ j * (Nat.choose (s + 1) j) = (-1) ^ t * Nat.choose s t := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [Finset.sum_range_succ, ih]
      have hp : (Nat.choose (s + 1) (t + 1) : ℝ) = Nat.choose s t + Nat.choose s (t + 1) := by
        rw [Nat.choose_succ_succ]
        push_cast
        ring
      rw [hp]
      ring

/-- The truncated alternating sum over subsets of a finset is at least the indicator of the
finset being empty, provided the truncation level is even. -/
