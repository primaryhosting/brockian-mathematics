/-
# Stone Generator
Category: Quantum Physics
Target: QPhys.stone_generator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Stone's theorem: the generator of a strongly continuous one-parameter unitary group

Let `H` be a complex Hilbert space and let `U : ℝ → H →L[ℂ] H` be a strongly continuous
one-parameter unitary group, i.e. `U 0 = 1`, `U (s + t) = U s * U t`, every `U t` is unitary,
and `t ↦ U t x` is continuous for every `x`.

The *generator* of `U` is the (in general unbounded) operator `A` whose domain consists of the
vectors `x` for which `t ↦ U t x` is differentiable at `0`, and which is given there by
`A x = -I • (d/dt)|_{t = 0} (U t x)`, so that formally `U t = exp (I * t * A)`.

The main result, `QPhys.stone_generator`, is that `A` is self-adjoint as a partially defined
operator (`LinearPMap`).

The proof follows the classical argument:

* `A` is symmetric, by differentiating `t ↦ ⟪U t x, U t y⟫`;
* `A ± I` are surjective, using the resolvent `x ↦ ∫ t in Ioi 0, exp (-t) • U t x`;
* consequently the domain of `A` is dense, and every symmetric operator with `A ± I` surjective
  is self-adjoint.
-/

open MeasureTheory Set

namespace QPhys

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The domain of the (infinitesimal) generator of a one-parameter family `U : ℝ → H →L[ℂ] H`:
the set of vectors `x` for which `t ↦ U t x` is differentiable at `0`. -/

theorem hasDerivAt_resolvent (hU : IsUnitaryGroup U) (x : H) :
    HasDerivAt (fun s : ℝ => U s (resolvent U x)) (resolvent U x - x) 0 := by
  set f : ℝ → H := fun t => Real.exp (-t) • U t x with hf
  have hfc : Continuous f :=
    (Real.continuous_exp.comp continuous_neg).smul (hU.strongly_continuous x)
  have hint : ∀ a : ℝ, IntegrableOn f (Ioi a) := by
    intro a
    refine Integrable.mono' (g := fun t : ℝ => Real.exp (-1 * t) * ‖x‖)
      ((exp_neg_integrableOn_Ioi a one_pos).mul_const ‖x‖) hfc.aestronglyMeasurable.restrict ?_
    filter_upwards with t
    simp [hf, norm_smul, hU.norm_map, Real.exp_nonneg, abs_of_nonneg]
  set R : H := ∫ t in Ioi (0 : ℝ), f t with hR
  set F : ℝ → H := fun s => ∫ t in (0 : ℝ)..s, f t with hFdef
  have hsplit : ∀ s : ℝ, ∫ u in Ioi s, f u = R - F s := by
    intro s
    rcases le_or_gt 0 s with hs | hs
    · have hunion : Ioi (0 : ℝ) = Ioc 0 s ∪ Ioi s := by rw [Ioc_union_Ioi_eq_Ioi hs]
      have h1 : R = (∫ u in Ioc (0 : ℝ) s, f u) + ∫ u in Ioi s, f u := by
        rw [hR, hunion, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
          ((hint 0).mono_set fun y hy => hy.1) (hint s)]
      rw [hFdef]
      simp only
      rw [intervalIntegral.integral_of_le hs, h1]
      abel
    · have hunion : Ioi s = Ioc s 0 ∪ Ioi (0 : ℝ) := by rw [Ioc_union_Ioi_eq_Ioi hs.le]
      have h1 : ∫ u in Ioi s, f u = (∫ u in Ioc s (0 : ℝ), f u) + R := by
        rw [hR, hunion, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
          ((hint s).mono_set fun y hy => hy.1) (hint 0)]
      rw [hFdef]
      simp only
      rw [intervalIntegral.integral_of_ge hs.le, h1]
      abel
  have htrans : ∀ (g : ℝ → H) (s : ℝ), ∫ t in Ioi (0 : ℝ), g (t + s) = ∫ u in Ioi s, g u := by
    intro g s
    rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
    have h : ∀ t : ℝ,
        (Ioi (0 : ℝ)).indicator (fun t => g (t + s)) t = (Ioi s).indicator g (t + s) := by
      intro t
      by_cases h : t ∈ Ioi (0 : ℝ)
      · rw [indicator_of_mem h, indicator_of_mem (show t + s ∈ Ioi s by simpa using h)]
      · rw [indicator_of_notMem h, indicator_of_notMem (show t + s ∉ Ioi s by simpa using h)]
    simp_rw [h]
    exact integral_add_right_eq_self (fun u => (Ioi s).indicator g u) s
  have key : ∀ s : ℝ, U s R = Real.exp s • (R - F s) := by
    intro s
    have h1 : U s R = ∫ t in Ioi (0 : ℝ), Real.exp s • f (t + s) := by
      rw [hR, ← ContinuousLinearMap.integral_comp_comm _ (hint 0)]
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
      rw [hf]
      simp only
      rw [ContinuousLinearMap.map_smul_of_tower, smul_smul]
      have e1 : Real.exp s * Real.exp (-(t + s)) = Real.exp (-t) := by
        rw [← Real.exp_add]; ring_nf
      have e2 : U (t + s) x = U s (U t x) := by rw [add_comm, hU.map_add]; rfl
      rw [e1, e2]
    rw [h1, integral_smul, htrans f s, hsplit s]
  have hF : HasDerivAt F (f 0) 0 :=
    intervalIntegral.integral_hasDerivAt_right (hfc.intervalIntegrable _ _)
      (hfc.stronglyMeasurableAtFilter _ _) hfc.continuousAt
  have hF0 : F 0 = 0 := by simp [hFdef]
  have hf0 : f 0 = x := by simp [hf, hU.map_zero]
  have hd : HasDerivAt (fun s : ℝ => Real.exp s • (R - F s))
      (Real.exp 0 • (0 - f 0) + Real.exp 0 • (R - F 0)) 0 :=
    (Real.hasDerivAt_exp 0).smul ((hasDerivAt_const (0 : ℝ) R).sub hF)
  have heq : Real.exp 0 • (0 - f 0) + Real.exp 0 • (R - F 0) = R - x := by
    rw [hF0, hf0]; simp; abel
  rw [heq] at hd
  have hfun : (fun s : ℝ => U s R) = fun s : ℝ => Real.exp s • (R - F s) := funext key
  show HasDerivAt (fun s : ℝ => U s R) (R - x) 0
  rw [hfun]
  exact hd

