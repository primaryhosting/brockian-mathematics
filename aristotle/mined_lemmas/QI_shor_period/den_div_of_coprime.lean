/-
# Shor Period
Category: Frontier Qi
Target: QI.shor_period
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Shor Period
Category: Frontier Qi
Target: QI.shor_period
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Shor's period-finding algorithm

This file formalises the mathematical content of Shor's period finding algorithm
for the modular exponentiation function `x ↦ a ^ x mod N`:

* the function is periodic with minimal period `r = orderOf (a : ZMod N)`;
* the quantum part: after the quantum Fourier transform of size `2 ^ n` is applied to
  the periodic superposition `∑_{j < M} |x₀ + j r⟩` (exact case `r * M = 2 ^ n`),
  the probability of measuring `c` is `1 / r` if `M ∣ c` and `0` otherwise, i.e.
  the measured `c` satisfies `c / 2 ^ n = s / r` for a uniformly random `s < r`;
* the classical post-processing: from a rational approximation of `s / r` within
  `1 / (2 R ^ 2)`, with `gcd (s, r) = 1` and `r ≤ R`, the denominator `r` is uniquely
  determined (this is the content of the continued fraction step);
* the success probability: the number of good `s < r` (those coprime to `r`) is
  `φ r`, so a single run succeeds with probability `φ r / r > 0`, and repeating
  the algorithm drives the failure probability to `0`.
-/

namespace QI

open Finset Complex
open scoped Classical

/-- The modular exponentiation function `x ↦ a ^ x` in `ZMod N`. -/

lemma den_div_of_coprime {s r : ℕ} (hr : 0 < r) (h : Nat.Coprime s r) :
    ((s : ℚ) / (r : ℚ)).den = r := by
  have hb : (0:ℤ) < (r:ℤ) := by exact_mod_cast hr
  have hd := Rat.den_div_eq_of_coprime (a := (s:ℤ)) (b := (r:ℤ)) hb (by simpa using h)
  have hcast : ((s:ℤ):ℚ) / ((r:ℤ):ℚ) = (s:ℚ)/(r:ℚ) := by push_cast; ring
  rw [hcast] at hd
  exact_mod_cast hd

/-- **Continued fraction step.**  If `x` approximates the reduced fraction `s / r` with
`r ≤ R` to within `1 / (2 R ^ 2)`, then `r` is uniquely determined by `x` and `R`, and the
post-processing returns it. -/
