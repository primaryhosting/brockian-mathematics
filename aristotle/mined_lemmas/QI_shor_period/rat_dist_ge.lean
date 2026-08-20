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

lemma rat_dist_ge {y z : ℚ} (h : y ≠ z) : 1 / ((y.den : ℚ) * z.den) ≤ |y - z| := by
  have hy : (0:ℚ) < y.den := by exact_mod_cast y.pos
  have hz : (0:ℚ) < z.den := by exact_mod_cast z.pos
  set A : ℤ := y.num * z.den - z.num * y.den with hA
  have key : (y - z) * ((y.den : ℚ) * z.den) = (A : ℚ) := by
    have h1 : (y.num : ℚ) = y * y.den := (Rat.mul_den_eq_num y).symm
    have h2 : (z.num : ℚ) = z * z.den := (Rat.mul_den_eq_num z).symm
    push_cast [hA, h1, h2]
    ring
  have hAne : A ≠ 0 := by
    intro h0
    apply h
    have hzero : (y - z) * ((y.den : ℚ) * z.den) = 0 := by rw [key, h0]; simp
    rcases mul_eq_zero.1 hzero with h' | h'
    · linarith [sub_eq_zero.1 h']
    · exact absurd h' (ne_of_gt (mul_pos hy hz))
  have h1A : (1:ℚ) ≤ |(A:ℚ)| := by
    have h1 : (1:ℤ) ≤ |A| := Int.one_le_abs (by omega)
    calc (1:ℚ) ≤ ((|A| : ℤ) : ℚ) := by exact_mod_cast h1
      _ = |(A:ℚ)| := by push_cast; ring
  rw [div_le_iff₀ (mul_pos hy hz)]
  calc (1:ℚ) ≤ |(A:ℚ)| := h1A
    _ = |y - z| * ((y.den:ℚ) * z.den) := by
        rw [← key, abs_mul, abs_of_pos (mul_pos hy hz)]

/-- A fraction `s / r` in lowest terms has denominator `r`. -/
