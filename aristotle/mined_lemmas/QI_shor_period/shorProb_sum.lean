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

lemma shorProb_sum {n r M x0 : ℕ} (h : r * M = 2 ^ n) :
    ∑ c ∈ Finset.range (2 ^ n), shorProb n r M x0 c = 1 := by
  have hpos : 0 < r * M := by rw [h]; exact Nat.two_pow_pos n
  have hr : 0 < r := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hpos
  have hM : 0 < M := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hpos
  have hrR : (0:ℝ) < r := by exact_mod_cast hr
  rw [← h]
  simp only [shorProb_eq h]
  rw [← Finset.sum_filter, Finset.sum_const, card_multiples_lt r M hM, nsmul_eq_mul]
  field_simp

/-! ### Part 3: classical post-processing (continued fractions) -/

/-- Two distinct rationals are at distance at least the inverse of the product of their
denominators. -/
