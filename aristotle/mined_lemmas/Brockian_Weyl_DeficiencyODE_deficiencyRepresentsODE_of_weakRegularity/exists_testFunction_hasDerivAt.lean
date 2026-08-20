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

import Brockian.Weyl.WeakDerivative

/-!
# Weyl deficiency spaces are represented by solutions of the Schrödinger ODE

For a continuous potential `q : ℝ → ℝ` and a spectral parameter `z : ℂ`, consider the
formally symmetric differential expression `τ u = -u'' + q u` on the line.  The minimal
operator is the restriction of `τ` to test functions, and the deficiency space at `z`
consists of the `L²` functions `u` which satisfy `τ u = z u` *weakly*, i.e. in the sense
of distributions:

  `∫ u φ'' = ∫ (q - z) u φ`   for all real test functions `φ`.

The main result of this file, `deficiencyRepresentsODE_of_weakRegularity`, states that
this deficiency space coincides with the set of `L²` functions which agree almost
everywhere with a *classical* (twice differentiable) solution of the ODE
`-u'' + q u = z u`.

The nontrivial inclusion is a regularity statement — every weak solution is almost
everywhere a classical solution — which is proved here from scratch (`weakRegularity`)
from the du Bois-Reymond lemmas of `Brockian.Weyl.WeakDerivative`; consequently the final

theorem exists_testFunction_hasDerivAt {ψ : ℝ → ℝ} (hψ : IsTestFunction ψ)
    (h0 : ∫ x : ℝ, ψ x = 0) :
    ∃ θ : ℝ → ℝ, IsTestFunction θ ∧ ∀ x, HasDerivAt θ (ψ x) x := by
  obtain ⟨R, hR0, hR⟩ := hψ.2.exists_pos_le_norm
  have hcont : Continuous ψ := hψ.continuous
  refine ⟨fun x => ∫ t in (-R)..x, ψ t, ⟨?_, ?_⟩, ?_⟩
  · refine contDiff_infty_iff_deriv.mpr ⟨fun x => ?_, ?_⟩
    · exact (intervalIntegral.integral_hasDerivAt_right (hcont.intervalIntegrable _ _)
        (hcont.stronglyMeasurableAtFilter _ _) hcont.continuousAt).differentiableAt
    · have hdeq : (deriv fun x => ∫ t in (-R)..x, ψ t) = ψ := funext fun x =>
        (intervalIntegral.integral_hasDerivAt_right (hcont.intervalIntegrable _ _)
          (hcont.stronglyMeasurableAtFilter _ _) hcont.continuousAt).deriv
      rw [hdeq]; exact hψ.1
  · refine HasCompactSupport.intro (K := Set.Icc (-R) R) isCompact_Icc ?_
    intro x hx
    simp only [Set.mem_Icc, not_and_or, not_le] at hx
    rcases hx with h | h
    · have hzero : Set.EqOn ψ (fun _ => (0 : ℝ)) (Set.uIcc (-R) x) := by
        intro t ht
        rw [Set.uIcc_comm, Set.uIcc_of_le h.le] at ht
        exact hR t (by
          rw [Real.norm_eq_abs, abs_of_nonpos (le_trans ht.2 (by linarith))]
          linarith [ht.2])
      rw [intervalIntegral.integral_congr hzero]
      simp
    · rw [intervalIntegral.integral_eq_integral_of_support_subset (a := -R) (b := x), h0]
      intro t ht
      have habs : |t| < R := by
        by_contra hc
        exact ht (hR t (by rw [Real.norm_eq_abs]; linarith [not_lt.mp hc]))
      rw [abs_lt] at habs
      exact ⟨habs.1, le_of_lt (lt_trans habs.2 h)⟩
  · exact fun x => intervalIntegral.integral_hasDerivAt_right (hcont.intervalIntegrable _ _)
      (hcont.stronglyMeasurableAtFilter _ _) hcont.continuousAt

/-- Integration by parts against a test function, for an everywhere differentiable
function with continuous derivative. -/
