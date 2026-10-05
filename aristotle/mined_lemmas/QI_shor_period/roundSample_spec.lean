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

lemma roundSample_spec {Q r s : ℕ} (hr : 0 < r) :
    2 * |(roundSample Q r s : ℤ) * r - s * Q| ≤ r := by
  have h2r : 0 < 2 * r := by omega
  have hd := Nat.div_add_mod (2 * s * Q + r) (2 * r)
  have hm := Nat.mod_lt (2 * s * Q + r) h2r
  set q := (2 * s * Q + r) / (2 * r) with hq
  set m := (2 * s * Q + r) % (2 * r) with hmm
  have hd' : (2 : ℤ) * r * q + m = 2 * s * Q + r := by exact_mod_cast hd
  have hm' : (m : ℤ) < 2 * r := by exact_mod_cast hm
  have hm0 : (0 : ℤ) ≤ m := Int.natCast_nonneg m
  have key : |2 * ((q : ℤ) * r - s * Q)| ≤ (r : ℤ) := abs_le.mpr ⟨by nlinarith, by nlinarith⟩
  calc 2 * |(q : ℤ) * r - s * Q| = |2 * ((q : ℤ) * r - s * Q)| := by rw [abs_mul]; norm_num
    _ ≤ (r : ℤ) := key

