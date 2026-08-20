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

theorem exists_tent {c d δ : ℝ} (hc : 0 ≤ c) (hd : d ≤ 1) (hδ : 0 < δ) :
    ∃ g : C(AddCircle (1 : ℝ), ℝ),
      (∀ x, 0 ≤ g x) ∧ (∀ x, g x ≤ 1) ∧
      (∀ x : ℝ, Int.fract x ∉ Ioo c d → g (x : AddCircle (1 : ℝ)) = 0) ∧
      d - c - 2 * δ ≤ ∫ x, g x ∂AddCircle.haarAddCircle := by
  -- the trapezoid on the real line
  set ψ : ℝ → ℝ := fun x => max 0 (min 1 (min ((x - c) / δ) ((d - x) / δ))) with hψ
  have hcont : Continuous ψ := by fun_prop
  have hψ0 : ∀ x, 0 ≤ ψ x := fun x => le_max_left _ _
  have hψ1 : ∀ x, ψ x ≤ 1 := fun x => max_le zero_le_one (min_le_left _ _)
  have hψsupp : ∀ x, x ∉ Ioo c d → ψ x = 0 := by
    intro x hx
    rw [mem_Ioo, not_and_or, not_lt, not_lt] at hx
    have hle : min 1 (min ((x - c) / δ) ((d - x) / δ)) ≤ 0 := by
      rcases hx with h | h
      · have hq : (x - c) / δ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le
        exact le_trans (min_le_right _ _) (le_trans (min_le_left _ _) hq)
      · have hq : (d - x) / δ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le
        exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) hq)
    simp only [hψ]
    exact max_eq_left hle
  have hψone : ∀ x, c + δ ≤ x → x ≤ d - δ → 1 ≤ ψ x := by
    intro x h1 h2
    have e1 : (1 : ℝ) ≤ (x - c) / δ := by rw [le_div_iff₀ hδ]; linarith
    have e2 : (1 : ℝ) ≤ (d - x) / δ := by rw [le_div_iff₀ hδ]; linarith
    simp only [hψ, min_eq_left (le_min e1 e2)]
    exact le_max_right _ _
  have hend : ψ 0 = ψ 1 := by
    rw [hψsupp 0 (by simp only [mem_Ioo, not_and, not_lt]; intro h; linarith),
      hψsupp 1 (by simp only [mem_Ioo, not_and, not_lt]; intro _; linarith)]
  -- transport it to the circle
  set g : C(AddCircle (1 : ℝ), ℝ) :=
    ⟨AddCircle.liftIco 1 0 ψ, AddCircle.liftIco_zero_continuous hend hcont.continuousOn⟩ with hg
  have hgcoe : ∀ x : ℝ, g (x : AddCircle (1 : ℝ)) = ψ (Int.fract x) := by
    intro x
    have h1 : ((Int.fract x : ℝ) : AddCircle (1 : ℝ)) = (x : AddCircle (1 : ℝ)) := by
      rw [Int.fract]; simp
    rw [← h1]
    simp only [hg, ContinuousMap.coe_mk]
    exact AddCircle.liftIco_zero_coe_apply ⟨Int.fract_nonneg x, Int.fract_lt_one x⟩
  refine ⟨g, ?_, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective x
    rw [show (QuotientAddGroup.mk z : AddCircle (1 : ℝ)) = ((z : ℝ) : AddCircle (1 : ℝ)) from rfl,
      hgcoe]
    exact hψ0 _
  · intro x
    obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective x
    rw [show (QuotientAddGroup.mk z : AddCircle (1 : ℝ)) = ((z : ℝ) : AddCircle (1 : ℝ)) from rfl,
      hgcoe]
    exact hψ1 _
  · intro x hx
    rw [hgcoe]
    exact hψsupp _ hx
  · -- the integral bound
    have hmeas : (AddCircle.haarAddCircle : Measure (AddCircle (1 : ℝ))) = volume := by
      rw [AddCircle.volume_eq_smul_haarAddCircle]; simp
    rw [hmeas, ← AddCircle.integral_preimage 1 0 g]
    have hcongr : (∫ a in Ioc (0 : ℝ) (0 + 1), g (a : AddCircle (1 : ℝ)))
        = ∫ a in Ioc (0 : ℝ) (0 + 1), ψ a := by
      refine setIntegral_congr_fun measurableSet_Ioc (fun a ha => ?_)
      show g (a : AddCircle (1 : ℝ)) = ψ a
      rw [hgcoe]
      rcases eq_or_lt_of_le ha.2 with h | h
      · rw [show a = 1 by simpa using h]
        simp [Int.fract, hend]
      · rw [Int.fract_eq_self.mpr ⟨ha.1.le, by simpa using h⟩]
    rw [hcongr, zero_add]
    rcases le_or_gt (d - c - 2 * δ) 0 with hsmall | hbig
    · exact le_trans hsmall (setIntegral_nonneg measurableSet_Ioc (fun a _ => hψ0 a))
    · have hsub : Ioc (c + δ) (d - δ) ⊆ Ioc (0 : ℝ) 1 := by
        apply Ioc_subset_Ioc <;> linarith
      have h1 : (∫ a in Ioc (c + δ) (d - δ), ψ a) ≤ ∫ a in Ioc (0 : ℝ) 1, ψ a :=
        setIntegral_mono_set hcont.integrableOn_Ioc (Filter.Eventually.of_forall hψ0)
          (HasSubset.Subset.eventuallyLE hsub)
      have h2 := setIntegral_ge_of_const_le (μ := (volume : Measure ℝ)) (c := (1 : ℝ))
        (s := Ioc (c + δ) (d - δ)) (f := ψ) measurableSet_Ioc (by simp [Real.volume_Ioc])
        (fun a ha => hψone a ha.1.le ha.2) hcont.integrableOn_Ioc
      rw [measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith), smul_eq_mul,
        mul_one] at h2
      linarith

/-! ### From continuous test functions to intervals -/

/-- The counting density rewritten as a Birkhoff average of an indicator. -/
