import Mathlib

/-!
# Shor Period
Category: Frontier Qi
Target: QI.shor_period
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Lean requires `import` lines to precede every other command, including module
doc comments, so this header follows the single `import Mathlib` line.)
-/

namespace QI

/-!
## Overview

Shor's algorithm finds the period `r` of the modular exponentiation function
`x ↦ a ^ x mod N` (for `a` coprime to `N`).  Its structure is:

* the function `x ↦ a ^ x mod N` really is periodic, with least period the
  multiplicative order `r` of `a` modulo `N`;
* the quantum phase-estimation stage produces, with probability bounded below by
  some constant `c > 0`, a measurement outcome `y` whose rescaling `y / M`
  approximates a fraction `s / r` with `gcd (s, r) = 1` to within `1 / (2 M)`
  (such an approximating outcome always exists, by rounding);
* the classical post-processing stage (continued fractions) then recovers `r`
  *exactly*, because a rational number with a sufficiently small denominator is
  uniquely determined by an approximation of this quality: any fraction `p / q`
  in lowest terms with `q * r < M` that is that close to `y / M` must have
  `q = r`;
* repeating the experiment amplifies the success probability to `1`.

The theorem `QI.shor_period` below bundles these statements.  The quantum stage
enters only through the abstract success probability `c`, since the amplitude
analysis is not part of the number-theoretic content formalized here.
-/

/-- Two rational numbers with small denominators cannot both be very close to the
same rational `x`: this is the uniqueness statement underlying the classical
continued-fraction post-processing of Shor's algorithm. -/

theorem approx_unique {x Q : ℚ} {p q s r : ℤ} (hq : 0 < q) (hr : 0 < r)
    (hQ : (q : ℚ) * r < Q ^ 2)
    (hp : |x - (p : ℚ) / q| ≤ 1 / (2 * Q ^ 2))
    (hs : |x - (s : ℚ) / r| ≤ 1 / (2 * Q ^ 2)) :
    (p : ℚ) / q = (s : ℚ) / r := by
  have hq' : (0:ℚ) < q := by exact_mod_cast hq
  have hr' : (0:ℚ) < r := by exact_mod_cast hr
  have hQ2 : (0:ℚ) < Q ^ 2 := lt_of_le_of_lt (by positivity) hQ
  by_contra hne
  have hdiff : |(p : ℚ) / q - (s : ℚ) / r| ≤ 1 / Q ^ 2 := by
    calc |(p : ℚ) / q - (s : ℚ) / r| ≤ |(p:ℚ)/q - x| + |x - (s:ℚ)/r| := abs_sub_le _ _ _
      _ ≤ 1/(2*Q^2) + 1/(2*Q^2) := by
          gcongr
          · rw [abs_sub_comm]; exact hp
      _ = 1/Q^2 := by field_simp; ring
  have hnum : ((p * r - s * q : ℤ) : ℚ) ≠ 0 := by
    intro h
    apply hne
    push_cast at h
    field_simp
    linarith
  have h1 : (1:ℚ) ≤ |((p * r - s * q : ℤ) : ℚ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs (by exact_mod_cast hnum)
  have heq : (p:ℚ)/q - (s:ℚ)/r = ((p*r - s*q : ℤ):ℚ)/((q:ℚ)*r) := by
    push_cast; field_simp
  rw [heq, abs_div, abs_of_pos (by positivity : (0:ℚ) < (q:ℚ)*r)] at hdiff
  have h2 : (1:ℚ)/((q:ℚ)*r) ≤ 1/Q^2 := le_trans (by gcongr) hdiff
  have hlt : (1:ℚ)/Q^2 < 1/((q:ℚ)*r) := one_div_lt_one_div_of_lt (by positivity) hQ
  linarith

/-- Equal fractions in lowest terms have equal (positive) denominators. -/
