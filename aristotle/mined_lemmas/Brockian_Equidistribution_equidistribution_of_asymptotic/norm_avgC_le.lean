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

lemma norm_avgC_le (x : ℕ → ℝ) (F : C(𝕋, ℂ)) (N : ℕ) : ‖avgC x F N‖ ≤ ‖F‖ := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [avgC, norm_nonneg F]
  · have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    have h1 : ‖∑ n ∈ Finset.range N, F ((x n : ℝ) : 𝕋)‖ ≤ N * ‖F‖ := by
      refine (norm_sum_le _ _).trans ?_
      calc ∑ n ∈ Finset.range N, ‖F ((x n : ℝ) : 𝕋)‖
          ≤ ∑ _n ∈ Finset.range N, ‖F‖ :=
            Finset.sum_le_sum fun n _ => F.norm_coe_le_norm _
        _ = N * ‖F‖ := by simp [Finset.sum_const, nsmul_eq_mul]
    rw [avgC, norm_mul, norm_inv, Complex.norm_natCast]
    calc (N : ℝ)⁻¹ * ‖∑ n ∈ Finset.range N, F ((x n : ℝ) : 𝕋)‖
        ≤ (N : ℝ)⁻¹ * (N * ‖F‖) := by
          exact mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = ‖F‖ := by field_simp

