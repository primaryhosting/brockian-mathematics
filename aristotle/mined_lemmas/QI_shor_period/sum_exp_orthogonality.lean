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

lemma sum_exp_orthogonality {Q : ℕ} (hQ : 0 < Q) {j j' : ℕ} (hj : j < Q) (hj' : j' < Q) :
    ∑ c ∈ range Q, Complex.exp (2 * Real.pi * Complex.I * (c * j) / Q) *
      (starRingEnd ℂ) (Complex.exp (2 * Real.pi * Complex.I * (c * j') / Q))
      = if j = j' then (Q : ℂ) else 0 := by
  have hQC : (Q : ℂ) ≠ 0 := by exact_mod_cast hQ.ne'
  set x : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) - j') / Q) with hx
  have hterm : ∀ c ∈ range Q, Complex.exp (2 * Real.pi * Complex.I * (c * j) / Q) *
      (starRingEnd ℂ) (Complex.exp (2 * Real.pi * Complex.I * (c * j') / Q)) = x ^ c := by
    intro c _
    rw [← Complex.exp_conj, ← Complex.exp_add, hx, ← Complex.exp_nat_mul]
    congr 1
    simp only [map_div₀, map_mul, map_ofNat, Complex.conj_I, Complex.conj_ofReal,
      Complex.conj_natCast]
    field_simp
    ring
  rw [Finset.sum_congr rfl hterm]
  have hxQ : x ^ Q = 1 := by
    rw [hx, ← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
    refine ⟨(j : ℤ) - j', ?_⟩
    push_cast
    field_simp
  by_cases hjj : j = j'
  · subst hjj
    simp [hx]
  · rw [if_neg hjj]
    have hxne : x ≠ 1 := by
      intro h
      rw [hx, Complex.exp_eq_one_iff] at h
      obtain ⟨n, hn⟩ := h
      field_simp at hn
      have h3 : ((j : ℤ) - j') = (Q : ℤ) * n := by exact_mod_cast hn
      have hdvd : (Q : ℤ) ∣ ((j : ℤ) - j') := ⟨n, h3⟩
      have habs : |((j : ℤ) - j')| < (Q : ℤ) := by
        rw [abs_lt]
        omega
      have h0 := Int.eq_zero_of_abs_lt_dvd hdvd habs
      omega
    rw [geom_sum_eq hxne, hxQ]
    simp

/-- Parseval for a single fibre. -/
