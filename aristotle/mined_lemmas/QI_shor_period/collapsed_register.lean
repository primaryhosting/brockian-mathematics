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

set_option grind.warning false

namespace QI

/-!
## Setting

We formalise the mathematical core of Shor's period–finding algorithm.

Fix a modulus `N`, an element `a` of order `r` modulo `N`, and a quantum register of
size `Q`.  Shor's algorithm prepares the uniform superposition
`Q^(-1/2) ∑_{x < Q} |x⟩ |a^x mod N⟩`, measures the second register — obtaining some value
`a^{x₀}` with `x₀ < r`, which collapses the first register to the uniform superposition over
the arithmetic progression `{x < Q : x ≡ x₀ [MOD r]}` — applies the quantum Fourier transform
of order `Q` to the first register and measures it.

The probability of observing the value `y` is therefore

  `prob Q r x₀ y = (m Q)⁻¹ * ‖∑_{j < m} exp(2πi (x₀ + j r) y / Q)‖²`,

where `m = numTerms Q r x₀` is the number of elements of the progression.  This is the
distribution `prob` defined below (`prob_sum_eq_one` verifies that it is a probability
distribution).

The theorems that constitute the correctness of the algorithm are:

* `QI.shor_period` : the measured value `y` lies, with probability at least
  `φ(r) / (6 r)`, in the set of outcomes from which the classical post-processing
  (best rational approximation with bounded denominator) returns the period `r`;
* `QI.shor_period_orderOf` : the same statement for `r = orderOf a`, i.e. for the period of
  the modular exponentiation function `x ↦ a ^ x`;
* `QI.recovers_unique` : that post-processing is well defined, i.e. an outcome `y`
  determines at most one period `r`;
* `QI.collapsed_register` : the set `{x < Q : a ^ x = a ^ x₀}` onto which the first register
  collapses is exactly the progression `{x₀ + j r : j < numTerms Q r x₀}`;
* `QI.prob_sum_eq_one` : `prob` is a probability distribution on the `Q` outcomes.
-/

/-- The number of `x < Q` with `x ≡ x₀ [MOD r]` and `x ≥ x₀`, i.e. `⌈(Q - x₀)/r⌉`. -/

theorem collapsed_register {G : Type*} [LeftCancelMonoid G] (a : G) {r Q x0 : ℕ}
    (hr : orderOf a = r) (h0 : 0 < r) (hx0 : x0 < r) (hQ : x0 < Q) :
    (Finset.range Q).filter (fun x => a ^ x = a ^ x0)
      = (Finset.range (numTerms Q r x0)).image (fun j => x0 + j * r) := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
  constructor
  · rintro ⟨hxQ, hax⟩
    rw [pow_eq_pow_iff_modEq, hr] at hax
    have hmod : x % r = x0 := by
      have hm : x % r = x0 % r := hax
      rwa [Nat.mod_eq_of_lt hx0] at hm
    have hdm := Nat.div_add_mod x r
    have hcomm : r * (x / r) = (x / r) * r := Nat.mul_comm _ _
    refine ⟨x / r, ?_, ?_⟩
    · rw [lt_numTerms_iff h0 hQ]
      omega
    · omega
  · rintro ⟨j, hj, rfl⟩
    rw [lt_numTerms_iff h0 hQ] at hj
    refine ⟨hj, ?_⟩
    rw [pow_eq_pow_iff_modEq, hr]
    show (x0 + j * r) % r = x0 % r
    simp [Nat.add_mul_mod_self_right]

