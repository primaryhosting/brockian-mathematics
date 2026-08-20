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

lemma recoverDen_eq {x : ℚ} {s r R : ℕ} (hr : 0 < r) (hrR : r ≤ R) (h : Nat.Coprime s r)
    (hx : |x - (s : ℚ) / (r : ℚ)| < 1 / (2 * (R : ℚ) ^ 2)) : recoverDen x R = r := by
  have hRpos : 0 < R := lt_of_lt_of_le hr hrR
  have hRQ : (0:ℚ) < R := by exact_mod_cast hRpos
  have hden0 : ((s : ℚ) / (r : ℚ)).den = r := den_div_of_coprime hr h
  have hex : ∃ y : ℚ, y.den ≤ R ∧ |x - y| < 1 / (2 * (R : ℚ) ^ 2) :=
    ⟨(s : ℚ) / (r : ℚ), by rw [hden0]; exact hrR, hx⟩
  rw [recoverDen, dif_pos hex]
  obtain ⟨hy1, hy2⟩ := hex.choose_spec
  set y := hex.choose with hyd
  by_cases hyy : y = (s : ℚ) / (r : ℚ)
  · rw [hyy, hden0]
  · exfalso
    have h1 : 1 / ((y.den : ℚ) * ((s : ℚ)/(r:ℚ)).den) ≤ |y - (s:ℚ)/(r:ℚ)| := rat_dist_ge hyy
    have h2 : |y - (s:ℚ)/(r:ℚ)| ≤ |x - y| + |x - (s:ℚ)/(r:ℚ)| := by
      have hrw : y - (s:ℚ)/(r:ℚ) = -(x - y) + (x - (s:ℚ)/(r:ℚ)) := by ring
      rw [hrw]
      calc |-(x - y) + (x - (s:ℚ)/(r:ℚ))| ≤ |-(x-y)| + |x - (s:ℚ)/(r:ℚ)| := abs_add_le _ _
        _ = |x - y| + |x - (s:ℚ)/(r:ℚ)| := by rw [abs_neg]
    have hdy : (0:ℚ) < y.den := by exact_mod_cast y.pos
    have hdyR : (y.den : ℚ) ≤ R := by exact_mod_cast hy1
    have hrQ : (r:ℚ) ≤ R := by exact_mod_cast hrR
    have hrQ0 : (0:ℚ) < r := by exact_mod_cast hr
    have h3 : 1 / ((R:ℚ) * R) ≤ 1 / ((y.den : ℚ) * ((s : ℚ)/(r:ℚ)).den) := by
      apply one_div_le_one_div_of_le (by positivity)
      rw [hden0]
      exact mul_le_mul hdyR hrQ (le_of_lt hrQ0) (le_of_lt hRQ)
    have h4 : |x - y| + |x - (s:ℚ)/(r:ℚ)| < 1 / ((R:ℚ)*R) := by
      have hsplit : (1:ℚ) / (2 * (R:ℚ)^2) + 1/(2*(R:ℚ)^2) = 1/((R:ℚ)*R) := by
        field_simp; ring
      linarith [hy2, hx]
    linarith

/-! ### Part 4: the success probability -/

/-- The number of outcomes `s < r` from which the period can be recovered is `φ r`. -/
