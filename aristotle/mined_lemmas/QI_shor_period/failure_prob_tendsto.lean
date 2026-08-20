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

lemma failure_prob_tendsto {r : ℕ} (hr : 0 < r) (ε : ℝ) (hε : 0 < ε) :
    ∃ k : ℕ, (1 - (Nat.totient r : ℝ) / r) ^ k < ε := by
  have h0 : 0 < (Nat.totient r : ℝ) / r := by
    have hpos : 0 < Nat.totient r := Nat.totient_pos.2 hr
    have hposR : (0:ℝ) < Nat.totient r := by exact_mod_cast hpos
    have hrR : (0:ℝ) < r := by exact_mod_cast hr
    positivity
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε (show (1 - (Nat.totient r : ℝ)/r) < 1 by linarith)
  exact ⟨k, hk⟩

/-! ### Main theorem -/

/-- **Shor's period finding algorithm.**

Let `a` be invertible modulo `N` and let `r` be the period of `x ↦ a ^ x mod N`.
Assume the exact case `r * M = 2 ^ n` for the quantum Fourier transform register size,
and `r ≤ R` for the classical bound `R`.  Then:

1. `x ↦ a ^ x mod N` is periodic with period `r`, and `r` is the least such period;
2. after the quantum Fourier transform, the outcome `c` is measured with probability
   `0` unless `M ∣ c`, and each `c = s * M` occurs with probability `1 / r`; these
   probabilities sum to `1`;
3. whenever the measured `s` is coprime to `r`, the classical post-processing applied to
   `c / 2 ^ n = s / r` returns exactly `r`;
4. the number of good values `s < r` is `φ r`, so a single run succeeds with probability
   `φ r / r > 0`, and repeated runs make the failure probability arbitrarily small:
   Shor's algorithm recovers the period with high probability. -/
