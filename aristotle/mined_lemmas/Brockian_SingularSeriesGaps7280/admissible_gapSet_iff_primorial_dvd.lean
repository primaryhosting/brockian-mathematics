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

theorem admissible_gapSet_iff_primorial_dvd (a d : ℤ) (k : ℕ) (hk : 0 < k) :
    Admissible (gapSet a d k) ↔ ((primorial k : ℕ) : ℤ) ∣ d := by
  rw [admissible_gapSet_iff a d k hk]
  constructor
  · intro h
    refine Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr ?_)
    refine Finset.prod_primes_dvd _ (fun q hq => (Finset.mem_filter.1 hq).2.prime) (fun q hq => ?_)
    rw [Finset.mem_filter, Finset.mem_range] at hq
    exact Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr (h q hq.2 (by omega)))
  · intro h p hp hpk
    have hdvd : p ∣ primorial k :=
      Finset.dvd_prod_of_mem _ (by simp [Finset.mem_filter, Finset.mem_range, hp]; omega)
    exact dvd_trans (Int.natCast_dvd_natCast.mpr hdvd) h

/-- A two-term gap range is the pair `{a, a + d}`. -/
