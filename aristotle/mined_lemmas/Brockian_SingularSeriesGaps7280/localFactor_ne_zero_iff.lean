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

lemma localFactor_ne_zero_iff (H : Finset ℤ) {p : ℕ} (hp : p.Prime) :
    localFactor H p ≠ 0 ↔ (residues H p).card < p := by
  refine ⟨fun h => ?_, fun h => ne_of_gt ((localFactor_pos_iff H hp).2 h)⟩
  by_contra hc
  push_neg at hc
  have hcard : (residues H p).card = p := le_antisymm (card_residues_le_prime H hp) hc
  have hp0 : (0 : ℝ) < p := by
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
    linarith
  apply h
  rw [localFactor, hcard, div_self (ne_of_gt hp0)]
  ring

/-- Admissibility is exactly the nonvanishing (equivalently, positivity) of all the local
factors of the singular series. -/
