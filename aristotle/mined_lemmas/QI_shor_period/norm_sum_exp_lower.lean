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

lemma norm_sum_exp_lower (θ : ℝ) (A : ℕ) :
    (A : ℝ) * (1 - θ ^ 2 * ((A : ℝ) ^ 2 - 1) / 24) ≤
      ‖∑ t ∈ range A, Complex.exp ((θ * t : ℝ) * Complex.I)‖ := by
  have hw : ‖Complex.exp ((-(θ * (((A : ℝ) - 1) / 2)) : ℝ) * Complex.I)‖ = 1 := by
    simp [Complex.norm_exp]
  have key : Complex.exp ((-(θ * (((A : ℝ) - 1) / 2)) : ℝ) * Complex.I) *
        (∑ t ∈ range A, Complex.exp ((θ * t : ℝ) * Complex.I))
      = ∑ t ∈ range A, Complex.exp ((θ * ((t : ℝ) - ((A : ℝ) - 1) / 2) : ℝ) * Complex.I) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hsum : ∑ t ∈ range A, (1 - (θ * ((t : ℝ) - ((A : ℝ) - 1) / 2)) ^ 2 / 2)
      = (A : ℝ) * (1 - θ ^ 2 * ((A : ℝ) ^ 2 - 1) / 24) := by
    have h1 : (∑ t ∈ range A, (1 - (θ * ((t : ℝ) - ((A : ℝ) - 1) / 2)) ^ 2 / 2))
        = (∑ _t ∈ range A, (1 : ℝ))
          - θ ^ 2 / 2 * ∑ t ∈ range A, ((t : ℝ) - ((A : ℝ) - 1) / 2) ^ 2 := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun t _ => by ring
    rw [h1, sum_centered_sq]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    ring
  calc (A : ℝ) * (1 - θ ^ 2 * ((A : ℝ) ^ 2 - 1) / 24)
      = ∑ t ∈ range A, (1 - (θ * ((t : ℝ) - ((A : ℝ) - 1) / 2)) ^ 2 / 2) := hsum.symm
    _ ≤ ∑ t ∈ range A, Real.cos (θ * ((t : ℝ) - ((A : ℝ) - 1) / 2)) :=
        Finset.sum_le_sum fun t _ => Real.one_sub_sq_div_two_le_cos
    _ = (∑ t ∈ range A, Complex.exp ((θ * ((t : ℝ) - ((A : ℝ) - 1) / 2) : ℝ) * Complex.I)).re := by
        rw [Complex.re_sum]
        exact Finset.sum_congr rfl fun t _ => (Complex.exp_ofReal_mul_I_re _).symm
    _ ≤ ‖∑ t ∈ range A, Complex.exp ((θ * ((t : ℝ) - ((A : ℝ) - 1) / 2) : ℝ) * Complex.I)‖ :=
        Complex.re_le_norm _
    _ = ‖Complex.exp ((-(θ * (((A : ℝ) - 1) / 2)) : ℝ) * Complex.I) *
          (∑ t ∈ range A, Complex.exp ((θ * t : ℝ) * Complex.I))‖ := by rw [key]
    _ = ‖∑ t ∈ range A, Complex.exp ((θ * t : ℝ) * Complex.I)‖ := by rw [norm_mul, hw, one_mul]

/-! ### Rewriting the Shor distribution as a sum over residue classes -/

