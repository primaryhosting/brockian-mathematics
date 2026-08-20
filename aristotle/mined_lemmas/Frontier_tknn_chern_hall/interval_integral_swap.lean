import Mathlib

/-!
# Tknn Chern Hall
Category: Frontier Physics
Target: Frontier.tknn_chern_hall
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

namespace Frontier

open MeasureTheory intervalIntegral

/-- The Berry curvature `F = ∂₁A₂ - ∂₂A₁` of a `U(1)` Berry connection `A = (A₁, A₂)`
on the Brillouin zone. -/

theorem interval_integral_swap (f : ℝ → ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hf : Continuous fun p : ℝ × ℝ => f p.1 p.2) :
    (∫ y in (0:ℝ)..L, ∫ x in (0:ℝ)..L, f x y)
      = ∫ x in (0:ℝ)..L, ∫ y in (0:ℝ)..L, f x y := by
  have hint : Integrable (Function.uncurry fun y x => f x y)
      ((volume.restrict (Set.Ioc (0:ℝ) L)).prod (volume.restrict (Set.Ioc (0:ℝ) L))) := by
    rw [Measure.prod_restrict]
    have hc : Continuous (Function.uncurry fun y x : ℝ => f x y) := by
      exact hf.comp (continuous_snd.prodMk continuous_fst)
    have hK : IntegrableOn (Function.uncurry fun y x : ℝ => f x y)
        (Set.Icc (0:ℝ) L ×ˢ Set.Icc (0:ℝ) L) volume :=
      (hc.continuousOn).integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
    exact hK.mono_set (Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self)
  have h1 : (∫ y in (0:ℝ)..L, ∫ x in (0:ℝ)..L, f x y)
      = ∫ y in Set.Ioc (0:ℝ) L, ∫ x in Set.Ioc (0:ℝ) L, f x y := by
    rw [intervalIntegral.integral_of_le hL]
    exact setIntegral_congr_fun measurableSet_Ioc
      (fun y _ => intervalIntegral.integral_of_le hL)
  have h2 : (∫ x in (0:ℝ)..L, ∫ y in (0:ℝ)..L, f x y)
      = ∫ x in Set.Ioc (0:ℝ) L, ∫ y in Set.Ioc (0:ℝ) L, f x y := by
    rw [intervalIntegral.integral_of_le hL]
    exact setIntegral_congr_fun measurableSet_Ioc
      (fun x _ => intervalIntegral.integral_of_le hL)
  rw [h1, h2]
  exact MeasureTheory.integral_integral_swap hint

/-- **Key lemma (Stokes / Green's theorem on the Brillouin zone).**
The integral of the Berry curvature over the square `[0, L] × [0, L]` equals the circulation
of the Berry connection around its boundary. -/
