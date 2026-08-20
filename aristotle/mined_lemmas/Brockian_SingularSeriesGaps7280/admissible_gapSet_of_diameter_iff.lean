import Mathlib

/-!
# Admissible gap ranges and the local factors of the singular series

A finite set `H ⊆ ℤ` (a *tuple*) is **admissible** when, for every prime `p`, the reductions
of the elements of `H` modulo `p` do not cover all of `ℤ/pℤ`.  This is exactly the condition
that every local factor

`localFactor H p = (1 - ν_H(p)/p) * (1 - 1/p)^(-|H|)`

of the Hardy–Littlewood singular series `𝔖(H) = ∏_p localFactor H p` is nonzero (equivalently,
positive), where `ν_H(p)` is the number of residue classes mod `p` occupied by `H`.

A **gap range** is a tuple of the shape `{a, a + d, a + 2d, …, a + (k-1)d}`: `k` points with
constant gap `d`.  The main results characterise which gap ranges are admissible, and in
particular determine all admissible gap ranges of diameter `7280`.
-/

namespace Brockian

/-- The set of residue classes mod `p` occupied by a tuple `H ⊆ ℤ`. -/

theorem admissible_gapSet_of_diameter_iff {D : ℤ} (h2 : (2 : ℤ) ∣ D) (h3 : ¬ ((3 : ℤ) ∣ D))
    (a d : ℤ) (k : ℕ) (hk : 2 ≤ k) (hdiam : d * ((k : ℤ) - 1) = D) :
    Admissible (gapSet a d k) ↔ k = 2 := by
  constructor
  · intro hadm
    by_contra hne
    have hk3 : 3 ≤ k := by omega
    have hd3 : (3 : ℤ) ∣ d :=
      (admissible_gapSet_iff a d k (by omega)).1 hadm 3 (by norm_num) hk3
    exact h3 (hdiam ▸ hd3.mul_right _)
  · rintro rfl
    have hd : d = D := by
      have : d * ((2 : ℤ) - 1) = D := by exact_mod_cast hdiam
      linarith
    subst hd
    exact admissible_gapSet_two h2

/-- **All admissible gap ranges of diameter `7280`.**

For a gap range with `k ≥ 2` terms, gap `d` and diameter `d * (k - 1) = 7280`, admissibility
holds if and only if `k = 2`; that is, the only admissible gap ranges of diameter `7280` with
at least two terms are the pairs `{a, a + 7280}`.  Moreover all local factors of the singular
series of such a pair are positive. -/
