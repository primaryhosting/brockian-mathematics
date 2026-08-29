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

lemma sum_sq_norm_eq {Q : ℕ} (hQ : 0 < Q) (S : Finset ℕ) (hS : S ⊆ range Q) :
    ∑ c ∈ range Q, ‖∑ j ∈ S, Complex.exp (2 * Real.pi * Complex.I * (c * j) / Q)‖ ^ 2
      = (Q : ℝ) * S.card := by
  have hcast : ((∑ c ∈ range Q,
        ‖∑ j ∈ S, Complex.exp (2 * Real.pi * Complex.I * (c * j) / Q)‖ ^ 2 : ℝ) : ℂ)
      = ((Q : ℝ) * S.card : ℝ) := by
    push_cast
    have step : ∀ c ∈ range Q,
        (((‖∑ j ∈ S, Complex.exp (2 * Real.pi * Complex.I * (c * j) / Q)‖ : ℝ) : ℂ)) ^ 2
        = ∑ j ∈ S, ∑ j' ∈ S, Complex.exp (2 * Real.pi * Complex.I * (c * j) / Q) *
            (starRingEnd ℂ) (Complex.exp (2 * Real.pi * Complex.I * (c * j') / Q)) := by
      intro c _
      rw [← Complex.ofReal_pow, Complex.sq_norm, ← Complex.mul_conj, map_sum, Finset.sum_mul_sum]
    rw [Finset.sum_congr rfl step, Finset.sum_comm]
    have h2 : ∀ j ∈ S, (∑ c ∈ range Q, ∑ j' ∈ S,
        Complex.exp (2 * Real.pi * Complex.I * (c * j) / Q) *
          (starRingEnd ℂ) (Complex.exp (2 * Real.pi * Complex.I * (c * j') / Q))) = (Q : ℂ) := by
      intro j hj
      rw [Finset.sum_comm]
      have h3 : ∀ j' ∈ S, (∑ c ∈ range Q,
          Complex.exp (2 * Real.pi * Complex.I * (c * j) / Q) *
            (starRingEnd ℂ) (Complex.exp (2 * Real.pi * Complex.I * (c * j') / Q)))
          = if j = j' then (Q : ℂ) else 0 :=
        fun j' hj' => sum_exp_orthogonality hQ (mem_range.mp (hS hj)) (mem_range.mp (hS hj'))
      rw [Finset.sum_congr rfl h3, Finset.sum_ite_eq S j (fun _ => (Q : ℂ))]
      simp [hj]
    rw [Finset.sum_congr rfl h2, Finset.sum_const, nsmul_eq_mul]
    ring
  exact_mod_cast hcast

/-- The Shor measurement outcome distribution has total mass one. -/
