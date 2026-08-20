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

/-
# Equidistribution Of Asymptotic
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Equidistribution Of Asymptotic
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(The block above is repeated as the file header; Lean does not allow a module docstring to
precede the `import` line.)

This file proves **Weyl's equidistribution criterion** unconditionally: if all nontrivial
exponential sums of a real sequence `x` are asymptotically negligible, then `x` is
equidistributed modulo one.  The argument goes through the circle `𝕋 = AddCircle 1`:

* the Birkhoff averages of each Fourier monomial converge to its integral (`avgC_fourier_tendsto`);
* the set of continuous functions with this property is a closed submodule of `C(𝕋, ℂ)`, hence,
  by Stone-Weierstrass (`span_fourier_closure_eq_top`), is everything (`avgC_tendsto`);
* indicator functions of arcs are squeezed between continuous plateau functions supported on
  metric balls, whose integrals are controlled by `AddCircle.volume_closedBall`.

As an application (and as a witness that the hypothesis is satisfiable) we derive the classical
equidistribution of irrational rotations, `equidistribution_irrational_rotation`.
-/

open Filter MeasureTheory Metric Complex Set
open scoped Topology Real BigOperators

namespace Brockian.Equidistribution

local notation "𝕋" => AddCircle (1 : ℝ)

/-- The Birkhoff/Weyl average of a complex-valued continuous function on the circle along the
first `N` terms of the sequence `x`. -/

lemma avgC_fourier_tendsto (x : ℕ → ℝ)
    (hW : ∀ k : ℤ, k ≠ 0 →
      Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N,
        Complex.exp (2 * π * Complex.I * k * x n)) atTop (𝓝 0)) (k : ℤ) :
    Tendsto (avgC x (fourier k)) atTop
      (𝓝 (∫ z : 𝕋, fourier k z ∂AddCircle.haarAddCircle)) := by
  rw [integral_fourier]
  by_cases hk : k = 0
  · subst hk
    have : ∀ N : ℕ, 1 ≤ N → avgC x (fourier 0) N = 1 := by
      intro N hN
      simp only [avgC, fourier_zero, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      rw [inv_mul_cancel₀]
      exact_mod_cast Nat.one_le_iff_ne_zero.mp hN
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN using (this N hN).symm
  · simp only [if_neg hk]
    have hEq : ∀ N : ℕ, avgC x (fourier k) N
        = (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, Complex.exp (2 * π * Complex.I * k * x n) := by
      intro N
      simp [avgC]
    exact (hW k hk).congr fun N => (hEq N).symm

/-! ### Step B: all continuous functions -/

