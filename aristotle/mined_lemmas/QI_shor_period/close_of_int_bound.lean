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

lemma close_of_int_bound {Q r c s : ℕ} (hr : 0 < r) (hQ : 0 < Q)
    (h : 2 * |(c : ℤ) * r - s * Q| ≤ r) : |(c : ℝ) / Q - (s : ℝ) / r| ≤ 1 / (2 * Q) := by
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have key : (c : ℝ) / Q - (s : ℝ) / r = (((c : ℤ) * r - s * Q : ℤ) : ℝ) / (Q * r) := by
    push_cast
    field_simp
  have habs : (|(c : ℤ) * r - s * Q| : ℝ) ≤ (r : ℝ) / 2 := by
    have h2 : ((2 * |(c : ℤ) * r - s * Q| : ℤ) : ℝ) ≤ ((r : ℤ) : ℝ) := by exact_mod_cast h
    push_cast at h2 ⊢
    linarith
  rw [key, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (Q : ℝ) * r)]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  push_cast at habs ⊢
  nlinarith [habs]

/-- Uniqueness of the rational approximation: if `c/Q` is within `1/(2Q)` of `s/r`
in lowest terms with `r ≤ M` and `M ^ 2 < Q`, no other fraction with denominator
at most `M` can be that close. -/
