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

import Mathlib

/-!
# Weyl's equidistribution theorem for irrational rotations

For an irrational number `a`, the fractional parts `{n * a}` are equidistributed in `[0,1)`:
for every subinterval `[u, v) ⊆ [0,1]` the proportion of `n < N` with `Int.fract (n * a) ∈ [u, v)`
tends to `v - u`.

The proof follows Weyl's method:

* `WeylSumsVanish a` is the statement that all non-trivial exponential (Weyl) sums along the
  orbit have vanishing averages;
* `tendsto_orbitAvg_of_weylSumsVanish` is the *conditional* statement that `WeylSumsVanish a`
  implies convergence of Birkhoff averages of continuous functions to their integral;
* `weylSumsVanish_of_irrational` *discharges* that hypothesis for irrational `a` (geometric
  series estimate), making the result unconditional;
* `equidistribution_of_asymptotic_exists` is the final unconditional interval version.
-/

namespace Brockian.Equidistribution

open Filter Topology MeasureTheory Set
open scoped BigOperators

noncomputable section

/-- Birkhoff / empirical average of a complex-valued function over the first `N` points of the
orbit of `0` under the rotation by `a` on the circle `ℝ / ℤ`. -/

theorem weylSumsVanish_of_irrational {a : ℝ} (ha : Irrational a) : WeylSumsVanish a := by
  intro k hk
  set z : ℂ := Complex.exp (2 * Real.pi * Complex.I * k * a) with hz
  have hnorm : ‖z‖ = 1 := by
    rw [hz, Complex.norm_exp]
    norm_num [Complex.ext_iff]
  have hzne : z ≠ 1 := by
    rw [hz]
    intro h
    rw [Complex.exp_eq_one_iff] at h
    obtain ⟨m, hm⟩ := h
    have h2 : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have hc : (k : ℂ) * a = m := by
      apply mul_left_cancel₀ h2
      linear_combination hm
    have hr : (k : ℝ) * a = (m : ℝ) := by exact_mod_cast hc
    exact (ha.intCast_mul hk).ne_int m hr
  have hterm : ∀ n : ℕ, (fourier k) ((n * a : ℝ) : AddCircle (1 : ℝ)) = z ^ n := by
    intro n
    rw [fourier_coe_apply, hz, ← Complex.exp_nat_mul]
    push_cast
    ring_nf
  have hz1 : (0 : ℝ) < ‖z - 1‖ := by
    simpa [sub_eq_zero] using hzne
  have hrw : ∀ N : ℕ, orbitAvg a (fourier k) N
      = (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, z ^ n := by
    intro N
    simp only [orbitAvg, hterm]
  simp only [hrw]
  refine squeeze_zero_norm (a := fun N : ℕ => (2 / ‖z - 1‖) / N) ?_
    (tendsto_const_div_atTop_nhds_zero_nat _)
  intro N
  have h2 : ‖z ^ N - 1‖ ≤ 2 := by
    calc ‖z ^ N - 1‖ ≤ ‖z ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by norm_num [norm_pow, hnorm]
  rw [norm_mul, norm_inv, geom_sum_eq hzne, norm_div, Complex.norm_natCast]
  show (N : ℝ)⁻¹ * (‖z ^ N - 1‖ / ‖z - 1‖) ≤ 2 / ‖z - 1‖ / N
  have he : (N : ℝ)⁻¹ * (‖z ^ N - 1‖ / ‖z - 1‖) = ‖z ^ N - 1‖ / ‖z - 1‖ / N := by ring
  rw [he]
  gcongr

/-! ### Elementary estimates -/

