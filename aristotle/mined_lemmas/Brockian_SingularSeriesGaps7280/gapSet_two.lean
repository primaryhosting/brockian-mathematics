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

lemma gapSet_two (a d : ℤ) : gapSet a d 2 = {a, a + d} := by
  ext x
  simp [gapSet, Finset.mem_image, Finset.mem_range, Nat.lt_succ_iff]
  constructor
  · rintro ⟨j, hj, rfl⟩
    interval_cases j <;> simp
  · rintro (rfl | rfl)
    · exact ⟨0, by norm_num⟩
    · exact ⟨1, by norm_num⟩

/-- **Admissible gap ranges of a given diameter.**  If the diameter `D` is even but not
divisible by `3`, then among gap ranges of diameter `D` with at least two terms exactly the
two-term ones (the pairs `{a, a + D}`) are admissible. -/
