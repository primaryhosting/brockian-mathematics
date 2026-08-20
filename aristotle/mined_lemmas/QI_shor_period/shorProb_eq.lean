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

lemma shorProb_eq {n r M x0 c : ℕ} (h : r * M = 2 ^ n) :
    shorProb n r M x0 c = if M ∣ c then 1 / (r : ℝ) else 0 := by
  have hpos : 0 < r * M := by rw [h]; exact Nat.two_pow_pos n
  have hr : 0 < r := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hpos
  have hM : 0 < M := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hpos
  have hsum : ∑ j ∈ Finset.range M, qftRoot n ^ ((x0 + j * r) * c)
      = qftRoot n ^ (x0 * c) * (if M ∣ c then (M:ℂ) else 0) := by
    rw [← geom_sum_qftRoot (r := r) h, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← pow_add]
    ring_nf
  rw [shorProb, qftAmp, hsum, norm_mul, norm_mul, mul_pow, mul_pow]
  have h1 : ‖qftRoot n ^ (x0 * c)‖ = 1 := by rw [norm_pow, norm_qftRoot, one_pow]
  have hinv : ‖((Real.sqrt ((M:ℝ) * 2 ^ n) : ℝ) : ℂ)⁻¹‖ = (Real.sqrt ((M:ℝ) * 2 ^ n))⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  rw [h1, hinv, one_pow, one_mul]
  have hMR : (0:ℝ) < M := by exact_mod_cast hM
  have hrR : (0:ℝ) < r := by exact_mod_cast hr
  have hsq : (Real.sqrt ((M:ℝ) * 2 ^ n)) ^ 2 = (M:ℝ) * 2 ^ n := Real.sq_sqrt (by positivity)
  have hcast : ((2:ℝ) ^ n) = (r : ℝ) * M := by
    have h2 : ((r * M : ℕ) : ℝ) = ((2 ^ n : ℕ) : ℝ) := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) h
    push_cast at h2
    linarith
  split_ifs with hd
  · rw [Complex.norm_natCast, inv_pow, hsq, hcast]
    field_simp
  · simp

/-- The number of multiples of `M` below `r * M` is `r`. -/
