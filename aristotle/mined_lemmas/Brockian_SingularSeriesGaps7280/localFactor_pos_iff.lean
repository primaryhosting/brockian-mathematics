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

lemma localFactor_pos_iff (H : Finset ℤ) {p : ℕ} (hp : p.Prime) :
    0 < localFactor H p ↔ (residues H p).card < p := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have h1 : 0 < 1 - 1 / (p : ℝ) := by
    have : 1 / (p : ℝ) ≤ 1 / 2 := by
      apply div_le_div_of_nonneg_left <;> linarith
    linarith
  have hzp : 0 < (1 - 1 / (p : ℝ)) ^ (-(H.card : ℤ)) := zpow_pos h1 _
  rw [localFactor, mul_pos_iff]
  constructor
  · rintro (⟨h, -⟩ | ⟨-, h⟩)
    · have : ((residues H p).card : ℝ) < p := by
        rw [sub_pos, div_lt_one hp0] at h; exact h
      exact_mod_cast this
    · linarith
  · intro h
    refine Or.inl ⟨?_, hzp⟩
    rw [sub_pos, div_lt_one hp0]
    exact_mod_cast h

/-- The local factor at a prime `p` is nonzero exactly when `H` misses a class mod `p`. -/
