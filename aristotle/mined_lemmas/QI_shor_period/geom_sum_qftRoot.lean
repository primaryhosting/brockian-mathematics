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

lemma geom_sum_qftRoot {n r M c : ℕ} (h : r * M = 2 ^ n) :
    ∑ j ∈ Finset.range M, qftRoot n ^ (j * r * c) = if M ∣ c then (M : ℂ) else 0 := by
  have hpos : 0 < r * M := by rw [h]; exact Nat.two_pow_pos n
  have hr : 0 < r := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hpos
  have hzeta : ∀ j : ℕ, qftRoot n ^ (j * r * c) = (qftRoot n ^ (r * c)) ^ j := by
    intro j
    rw [← pow_mul]
    ring_nf
  simp only [hzeta]
  by_cases hd : M ∣ c
  · have h1 : qftRoot n ^ (r * c) = 1 := by
      rw [qftRoot_pow_eq_one_iff, ← h]
      exact mul_dvd_mul_left r hd
    simp [h1, hd]
  · have h1 : qftRoot n ^ (r * c) ≠ 1 := by
      rw [Ne, qftRoot_pow_eq_one_iff, ← h]
      intro hcon
      exact hd ((mul_dvd_mul_iff_left (a := r) hr.ne').1 hcon)
    have h2 : (qftRoot n ^ (r * c)) ^ M = 1 := by
      rw [← pow_mul, qftRoot_pow_eq_one_iff, ← h]
      exact ⟨c, by ring⟩
    rw [geom_sum_eq h1, h2, if_neg hd]
    simp

/-- **The measurement statistics of Shor's algorithm** (exact case `r * M = 2 ^ n`):
the outcome `c` occurs with probability `1 / r` if `M ∣ c`, and with probability `0`
otherwise. -/
