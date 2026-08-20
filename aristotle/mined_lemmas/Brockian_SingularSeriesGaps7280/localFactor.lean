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

noncomputable def localFactor (H : Finset ℤ) (p : ℕ) : ℝ :=
  (1 - ((residues H p).card : ℝ) / p) * (1 - 1 / (p : ℝ)) ^ (-(H.card : ℤ))

/-- A *gap range*: the `k`-tuple `{a, a + d, …, a + (k-1)d}` with first term `a` and gap `d`. -/
