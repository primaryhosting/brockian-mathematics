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

theorem shor_period (N a n R r M x0 : ℕ) (hN : 1 < N) (ha : Nat.Coprime a N)
    (hr : r = period N a) (hrM : r * M = 2 ^ n) (hrR : r ≤ R) :
    -- (1) periodicity with minimal period `r`
    (0 < r ∧ (∀ x : ℕ, modExp N a (x + r) = modExp N a x) ∧
      (∀ t : ℕ, 0 < t → t < r → modExp N a t ≠ modExp N a 0)) ∧
    -- (2) the measurement statistics of the quantum part
    ((∀ c : ℕ, ¬ M ∣ c → shorProb n r M x0 c = 0) ∧
      (∀ s : ℕ, shorProb n r M x0 (s * M) = 1 / (r : ℝ)) ∧
      ∑ c ∈ Finset.range (2 ^ n), shorProb n r M x0 c = 1) ∧
    -- (3) the classical post-processing recovers `r` exactly from a good outcome
    (∀ s : ℕ, Nat.Coprime s r →
      recoverDen (((s * M : ℕ) : ℚ) / ((2 ^ n : ℕ) : ℚ)) R = r) ∧
    -- (4) the success probability of one run, and amplification by repetition
    (((Finset.range r).filter (fun s => Nat.Coprime s r)).card = Nat.totient r ∧
      0 < (Nat.totient r : ℝ) / r ∧
      ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, (1 - (Nat.totient r : ℝ) / r) ^ k < ε) := by
  subst hr
  have hrpos : 0 < period N a := period_pos hN ha
  refine ⟨⟨hrpos, fun x => modExp_periodic N a x, fun t ht htr => modExp_ne_of_lt_period t ht htr⟩,
    ⟨fun c hc => by rw [shorProb_eq hrM, if_neg hc],
     fun s => by rw [shorProb_eq hrM, if_pos ⟨s, mul_comm s M⟩],
     shorProb_sum hrM⟩, ?_, card_good_outcomes _, ?_, failure_prob_tendsto hrpos⟩
  · intro s hs
    have hkey : ((s * M : ℕ) : ℚ) / ((2 ^ n : ℕ) : ℚ) = (s : ℚ) / ((period N a : ℕ) : ℚ) := by
      rw [← hrM]
      have hMpos : 0 < M := Nat.pos_of_ne_zero fun h0 => by
        rw [h0, mul_zero] at hrM
        exact absurd hrM.symm (Nat.two_pow_pos n).ne'
      have hM' : (M : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hMpos.ne'
      push_cast
      rw [mul_comm ((period N a : ℚ)) (M : ℚ), ← div_div, mul_div_assoc, mul_comm,
        mul_div_assoc, div_self hM', one_mul]
    rw [hkey]
    refine recoverDen_eq hrpos hrR hs ?_
    have hRpos : 0 < (R : ℚ) := by exact_mod_cast lt_of_lt_of_le hrpos hrR
    simp only [sub_self, abs_zero]
    positivity
  · have := Nat.totient_pos.2 hrpos
    positivity

end QI

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

