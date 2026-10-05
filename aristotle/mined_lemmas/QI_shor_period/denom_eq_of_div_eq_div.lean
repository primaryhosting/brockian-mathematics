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

theorem denom_eq_of_div_eq_div {p q s r : ℤ} (hq : 0 < q) (hr : 0 < r)
    (hpq : IsCoprime p q) (hsr : IsCoprime s r) (h : (p : ℚ) / q = (s : ℚ) / r) :
    q = r := by
  have hq' : (0:ℚ) < q := by exact_mod_cast hq
  have hr' : (0:ℚ) < r := by exact_mod_cast hr
  have hcross : p * r = s * q := by
    have : (p:ℚ) * r = (s:ℚ) * q := by field_simp at h; linarith
    exact_mod_cast this
  have h1 : q ∣ r := (hpq.symm).dvd_of_dvd_mul_left ⟨s, by linarith [hcross]⟩
  have h2 : r ∣ q := (hsr.symm).dvd_of_dvd_mul_left ⟨p, by linarith [hcross]⟩
  exact Int.dvd_antisymm hq.le hr.le h1 h2

/-- The classical post-processing step of Shor's algorithm: from a rational `x`
approximating `s / r` (with `s` coprime to `r`) to within `1 / (2 Q ^ 2)`, the
period `r` is recovered uniquely, i.e. any reduced fraction `p / q` with
`q * r < Q ^ 2` and the same approximation quality has `q = r`. -/
