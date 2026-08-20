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

theorem six_dvd_diameter_of_admissible {a d : ℤ} {k : ℕ} (hk : 3 ≤ k)
    (h : Admissible (gapSet a d k)) : (6 : ℤ) ∣ d * ((k : ℤ) - 1) := by
  have hk0 : 0 < k := by omega
  have hall := (admissible_gapSet_iff a d k hk0).1 h
  have h2 : (2 : ℤ) ∣ d := by exact_mod_cast hall 2 (by norm_num) (by omega)
  have h3 : (3 : ℤ) ∣ d := by exact_mod_cast hall 3 (by norm_num) (by omega)
  have h6 : (6 : ℤ) ∣ d := by omega
  exact h6.mul_right _

/-- **Primorial form of the characterisation.**  A nonempty gap range is admissible exactly
when its gap is divisible by the primorial `k#` (the product of all primes `≤ k`). -/
