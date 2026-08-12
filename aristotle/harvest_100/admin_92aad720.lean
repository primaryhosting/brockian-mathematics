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
# Deficiency Represents ODE Of Weak Regularity
Category: Brockian (Literature Discharge)
Target: Brockian.Weyl.DeficiencyODE.deficiencyRepresentsODE_of_weakRegularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.Weyl.DeficiencyODE

open intervalIntegral MeasureTheory

/-- Weak (integrated / "first-order system") form of the deficiency equation
`-u'' + q u = z u` for a Sturm–Liouville expression with continuous potential `q`.

Here `v` plays the role of the quasi-derivative `u'`: the pair `(u, v)` is required to be
continuous and to satisfy the two integral identities that express, in the weakest reasonable
sense, that `u' = v` and `v' = (q - z) u`.  Elements of the deficiency space of the minimal
operator at the spectral parameter `z` satisfy exactly these relations. -/
structure IsWeakDeficiencySolution (q : ℝ → ℂ) (z : ℂ) (u v : ℝ → ℂ) : Prop where
  contU : Continuous u
  contV : Continuous v
  integral_u : ∀ x : ℝ, u x = u 0 + ∫ t in (0:ℝ)..x, v t
  integral_v : ∀ x : ℝ, v x = v 0 + ∫ t in (0:ℝ)..x, (q t - z) * u t

/-- Classical (strong) form of the deficiency equation: `u` is differentiable with derivative
`v`, and `v` is differentiable with derivative `(q - z) u`, i.e. `-u'' + q u = z u`. -/
def IsClassicalDeficiencySolution (q : ℝ → ℂ) (z : ℂ) (u v : ℝ → ℂ) : Prop :=
  (∀ x : ℝ, HasDerivAt u (v x) x) ∧ (∀ x : ℝ, HasDerivAt v ((q x - z) * u x) x)

/-- **Deficiency elements represent the ODE, assuming only weak regularity.**

For a continuous potential `q` and any spectral parameter `z`, a pair `(u, v)` satisfies the
weak (integrated) form of the deficiency equation `-u'' + q u = z u` if and only if it satisfies
the classical form: `u` is differentiable with `u' = v` and `v` is differentiable with
`v' = (q - z) u`.  In particular no extra regularity hypothesis is needed: weak solutions are
automatically classical (indeed `C¹`) solutions.

The proof is the fundamental theorem of calculus in both directions
(`intervalIntegral.integral_hasDerivAt_right` and
`intervalIntegral.integral_eq_sub_of_hasDerivAt`). -/
theorem deficiencyRepresentsODE_of_weakRegularity
    (q : ℝ → ℂ) (hq : Continuous q) (z : ℂ) (u v : ℝ → ℂ) :
    IsWeakDeficiencySolution q z u v ↔ IsClassicalDeficiencySolution q z u v := by
  constructor
  · rintro ⟨hu, hv, hiu, hiv⟩
    have hf : Continuous fun t : ℝ => (q t - z) * u t := (hq.sub continuous_const).mul hu
    constructor
    · intro x
      have h1 : HasDerivAt (fun y : ℝ => ∫ t in (0:ℝ)..y, v t) (v x) x :=
        integral_hasDerivAt_right (hv.intervalIntegrable 0 x)
          (hv.stronglyMeasurableAtFilter _ _) hv.continuousAt
      have h2 : HasDerivAt (fun y : ℝ => u 0 + ∫ t in (0:ℝ)..y, v t) (v x) x := by
        simpa using h1.const_add (u 0)
      exact h2.congr_of_eventuallyEq (Filter.Eventually.of_forall hiu)
    · intro x
      have h1 : HasDerivAt (fun y : ℝ => ∫ t in (0:ℝ)..y, (q t - z) * u t)
          ((q x - z) * u x) x :=
        integral_hasDerivAt_right (hf.intervalIntegrable 0 x)
          (hf.stronglyMeasurableAtFilter _ _) hf.continuousAt
      have h2 : HasDerivAt (fun y : ℝ => v 0 + ∫ t in (0:ℝ)..y, (q t - z) * u t)
          ((q x - z) * u x) x := by
        simpa using h1.const_add (v 0)
      exact h2.congr_of_eventuallyEq (Filter.Eventually.of_forall hiv)
  · rintro ⟨hu, hv⟩
    have hcu : Continuous u := continuous_iff_continuousAt.2 fun x => (hu x).continuousAt
    have hcv : Continuous v := continuous_iff_continuousAt.2 fun x => (hv x).continuousAt
    have hf : Continuous fun t : ℝ => (q t - z) * u t := (hq.sub continuous_const).mul hcu
    refine ⟨hcu, hcv, ?_, ?_⟩
    · intro x
      have h := integral_eq_sub_of_hasDerivAt (f := u) (f' := v) (a := 0) (b := x)
        (fun t _ => hu t) (hcv.intervalIntegrable 0 x)
      rw [h]; ring
    · intro x
      have h := integral_eq_sub_of_hasDerivAt (f := v) (f' := fun t => (q t - z) * u t)
        (a := 0) (b := x) (fun t _ => hv t) (hf.intervalIntegrable 0 x)
      rw [h]; ring

end Brockian.Weyl.DeficiencyODE

