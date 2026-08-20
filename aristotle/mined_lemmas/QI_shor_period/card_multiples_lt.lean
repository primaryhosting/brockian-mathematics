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

lemma card_multiples_lt (r M : ℕ) (hM : 0 < M) :
    ((Finset.range (r * M)).filter (fun c => M ∣ c)).card = r := by
  have himg : ((Finset.range (r * M)).filter (fun c => M ∣ c))
      = (Finset.range r).image (fun s => s * M) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hc, k, rfl⟩
      exact ⟨k, by nlinarith [hc], by ring⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨by nlinarith, ⟨s, mul_comm _ _⟩⟩
  rw [himg, Finset.card_image_of_injective _ (fun x y hxy => by
    simpa [Nat.mul_left_inj hM.ne'] using hxy), Finset.card_range]

/-- The measurement probabilities sum to `1`: they do form a probability distribution. -/
