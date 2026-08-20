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

theorem tendsto_orbitAvg_of_weylSumsVanish {a : ℝ} (h : WeylSumsVanish a)
    (f : C(AddCircle (1 : ℝ), ℂ)) :
    Tendsto (orbitAvg a f) atTop (𝓝 (∫ x, f x ∂AddCircle.haarAddCircle)) := by
  have hspan : ∀ g ∈ Submodule.span ℂ (Set.range (fourier (T := (1 : ℝ)))),
      Tendsto (orbitAvg a g) atTop (𝓝 (∫ x, g x ∂AddCircle.haarAddCircle)) := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨k, rfl⟩ := hx
        rcases eq_or_ne k 0 with rfl | hk
        · have hint : (∫ x : AddCircle (1 : ℝ), fourier 0 x ∂AddCircle.haarAddCircle) = 1 := by
            simp
          rw [hint]
          refine Tendsto.congr' ?_ tendsto_const_nhds
          filter_upwards [eventually_ge_atTop 1] with N hN
          have hNR : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
          simp only [orbitAvg, fourier_zero, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
            mul_one]
          field_simp
        · rw [integral_fourier_ne_zero hk]
          exact h k hk
    | zero =>
        have hz : ∀ N, orbitAvg a (0 : C(AddCircle (1 : ℝ), ℂ)) N = 0 := by
          intro N; simp [orbitAvg]
        have h0 : (∫ x, (0 : C(AddCircle (1 : ℝ), ℂ)) x ∂AddCircle.haarAddCircle) = 0 := by simp
        rw [h0]
        exact Tendsto.congr (fun N => (hz N).symm) tendsto_const_nhds
    | add u v _ _ hu hv =>
        have hsum : ∀ N, orbitAvg a (u + v) N = orbitAvg a u N + orbitAvg a v N := by
          intro N
          simp only [orbitAvg, Pi.add_apply, Finset.sum_add_distrib, mul_add]
        have hint : (∫ x, (u + v) x ∂AddCircle.haarAddCircle)
            = (∫ x, u x ∂AddCircle.haarAddCircle) + ∫ x, v x ∂AddCircle.haarAddCircle := by
          simp only [ContinuousMap.add_apply]
          exact integral_add (integrable_of_continuousMap u) (integrable_of_continuousMap v)
        rw [hint]
        exact Tendsto.congr (fun N => (hsum N).symm) (hu.add hv)
    | smul c u _ hu =>
        have hsum : ∀ N, orbitAvg a (c • u) N = c * orbitAvg a u N := by
          intro N
          simp only [orbitAvg, Pi.smul_apply, smul_eq_mul]
          rw [← Finset.mul_sum]
          ring
        have hint : (∫ x, (c • u) x ∂AddCircle.haarAddCircle)
            = c * ∫ x, u x ∂AddCircle.haarAddCircle := by
          simp only [ContinuousMap.smul_apply, smul_eq_mul]
          simpa using integral_smul c (fun x => u x)
        rw [hint]
        exact Tendsto.congr (fun N => (hsum N).symm) (hu.const_mul c)
  have hd : Dense ((Submodule.span ℂ (Set.range (fourier (T := (1 : ℝ)))) :
      Submodule ℂ C(AddCircle (1 : ℝ), ℂ)) : Set C(AddCircle (1 : ℝ), ℂ)) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top]
    exact span_fourier_closure_eq_top
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨g, hgmem, hgd⟩ := hd.exists_dist_lt f (by linarith : (0:ℝ) < ε / 3)
  obtain ⟨N₀, hN₀⟩ := (Metric.tendsto_atTop.mp (hspan g hgmem)) (ε / 3) (by linarith)
  refine ⟨N₀, fun N hN => ?_⟩
  have h1 : ‖orbitAvg a f N - orbitAvg a g N‖ ≤ ‖f - g‖ := norm_orbitAvg_sub_le a f g N
  have h2 : dist (orbitAvg a g N) (∫ x, g x ∂AddCircle.haarAddCircle) < ε / 3 := hN₀ N hN
  have h3 : ‖(∫ x, g x ∂AddCircle.haarAddCircle) - ∫ x, f x ∂AddCircle.haarAddCircle‖ ≤ ‖g - f‖ :=
    norm_integral_sub_le g f
  have hfg : ‖f - g‖ < ε / 3 := by rwa [← dist_eq_norm]
  have hgf : ‖g - f‖ < ε / 3 := by rw [← dist_eq_norm, dist_comm]; exact hgd
  have hkey := dist_triangle4 (orbitAvg a f N) (orbitAvg a g N)
    (∫ x, g x ∂AddCircle.haarAddCircle) (∫ x, f x ∂AddCircle.haarAddCircle)
  rw [dist_eq_norm (orbitAvg a f N) (orbitAvg a g N),
    dist_eq_norm (∫ x, g x ∂AddCircle.haarAddCircle) (∫ x, f x ∂AddCircle.haarAddCircle)] at hkey
  linarith

/-- Unconditional version for continuous complex-valued test functions. -/
