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

theorem admissible_gapSet_iff (a d : ℤ) (k : ℕ) (hk : 0 < k) :
    Admissible (gapSet a d k) ↔ ∀ p : ℕ, p.Prime → p ≤ k → (p : ℤ) ∣ d := by
  constructor
  · intro h p hp hpk
    by_contra hd
    have hcard := residues_gapSet_of_not_dvd (a := a) hp hpk hd
    have hlt := h p hp
    omega
  · intro h p hp
    by_cases hd : (p : ℤ) ∣ d
    · rw [residues_gapSet_of_dvd hk hd]
      simpa using hp.one_lt
    · have hpk : k < p := by
        by_contra hc
        exact hd (h p hp (not_lt.1 hc))
      calc (residues (gapSet a d k) p).card ≤ (gapSet a d k).card := card_residues_le _ _
        _ ≤ (Finset.range k).card := Finset.card_image_le
        _ = k := Finset.card_range k
        _ < p := hpk

/-- Every gap range of two terms with an even gap is admissible. -/
