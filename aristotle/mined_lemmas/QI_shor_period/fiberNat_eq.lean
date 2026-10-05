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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QI

open Finset Complex

/-!
## The Shor sampling distribution

We model the period-finding core of Shor's algorithm.  Fix a modulus `N`, a unit
`u : (ZMod N)ˣ` and a power-of-two-sized (any size, really) register `Q`.
The algorithm prepares

  `Q^{-1/2} ∑_{j < Q} |j⟩ |u ^ j⟩`,

applies the quantum Fourier transform modulo `Q` to the first register and
measures.  The probability of observing `c` in the first register and `y` in the
second one is `Q^{-2} ‖∑_{j < Q, u ^ j = y} e^{2πι c j / Q}‖^2`, so the marginal
probability of observing `c` is the following quantity.
-/

/-- Probability that Shor's period-finding circuit, run with modulus `N`, base `u`
and register size `Q`, outputs the value `c`. -/

lemma fiberNat_eq {Q r k : ℕ} (hr : 0 < r) (hk : k < Q) (hkr : k < r) :
    (range Q).filter (fun j => j % r = k) = (range (blockCount Q r k)).image (fun t => k + t * r) := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
  have hq : j / r * r + j % r = j := Nat.div_add_mod' j r
  constructor
  · rintro ⟨hjQ, hj⟩
    refine ⟨j / r, ?_, by omega⟩
    rw [lt_blockCount_iff hr hk]
    omega
  · rintro ⟨t, ht, rfl⟩
    rw [lt_blockCount_iff hr hk] at ht
    exact ⟨ht, by simp [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hkr]⟩

