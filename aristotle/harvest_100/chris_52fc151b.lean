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


open MeasureTheory

namespace Brockian.Weyl.DeficiencyODE

/-- A *weak* (Carathéodory / integrated form) solution of the Sturm–Liouville equation
`u'' = (q - z) u` on the whole line: there is a continuous "quasi-derivative" `v` such that
`u` is the primitive of `v` and `v` is the primitive of `(q - z) u`.

This is the regularity that is available a priori for elements of the deficiency space of the
minimal operator `L u = -u'' + q u`: such an element is only known to solve the equation in the
integrated (distributional) sense. -/
def IsWeakSolution (q : ℝ → ℂ) (z : ℂ) (u : ℝ → ℂ) : Prop :=
  ∃ v : ℝ → ℂ, Continuous v ∧
    (∀ x, u x = u 0 + ∫ t in (0:ℝ)..x, v t) ∧
    (∀ x, v x = v 0 + ∫ t in (0:ℝ)..x, (q t - z) * u t)

/-- A *classical* (pointwise, twice differentiable) solution of `u'' = (q - z) u`. -/
def IsClassicalSolution (q : ℝ → ℂ) (z : ℂ) (u : ℝ → ℂ) : Prop :=
  ∃ v : ℝ → ℂ, (∀ x, HasDerivAt u (v x) x) ∧ (∀ x, HasDerivAt v ((q x - z) * u x) x)

/-- The deficiency space at `z` of the minimal Sturm–Liouville operator with potential `q`:
the square-integrable weak solutions of `u'' = (q - z) u`.  (For `z = ± Complex.I` this is the
space computing the classical Weyl deficiency indices.) -/
def deficiencySpace (q : ℝ → ℂ) (z : ℂ) : Set (ℝ → ℂ) :=
  {u | MemLp u 2 (volume : Measure ℝ) ∧ IsWeakSolution q z u}

/-- The space of square-integrable *classical* solutions of `u'' = (q - z) u`. -/
def odeSolutionSpace (q : ℝ → ℂ) (z : ℂ) : Set (ℝ → ℂ) :=
  {u | MemLp u 2 (volume : Measure ℝ) ∧ IsClassicalSolution q z u}

/-- A function that is everywhere differentiable is continuous. -/
theorem continuous_of_hasDerivAt {f g : ℝ → ℂ} (h : ∀ x, HasDerivAt f (g x) x) :
    Continuous f :=
  continuous_iff_continuousAt.2 fun x => (h x).continuousAt

/-- If a function is the primitive of a continuous function, it is everywhere differentiable
with the expected derivative.  (Second fundamental theorem of calculus,
`intervalIntegral.integral_hasDerivAt_right`.) -/
theorem hasDerivAt_of_primitive_rep {f g : ℝ → ℂ} (hg : Continuous g)
    (h : ∀ x, f x = f 0 + ∫ t in (0:ℝ)..x, g t) (x : ℝ) : HasDerivAt f (g x) x := by
  have hprim : HasDerivAt (fun y : ℝ => ∫ t in (0:ℝ)..y, g t) (g x) x :=
    intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable _ _)
      (hg.stronglyMeasurableAtFilter _ _) hg.continuousAt
  have h2 : HasDerivAt (fun y : ℝ => f 0 + ∫ t in (0:ℝ)..y, g t) (g x) x := by
    simpa using hprim.const_add (f 0)
  have hf : f = fun y : ℝ => f 0 + ∫ t in (0:ℝ)..y, g t := funext h
  rw [hf]
  exact h2

/-- Conversely, a function with a continuous derivative is the primitive of that derivative.
(First fundamental theorem of calculus, `intervalIntegral.integral_eq_sub_of_hasDerivAt`.) -/
theorem primitive_rep_of_hasDerivAt {f g : ℝ → ℂ} (hg : Continuous g)
    (h : ∀ x, HasDerivAt f (g x) x) (x : ℝ) : f x = f 0 + ∫ t in (0:ℝ)..x, g t := by
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := f) (f' := g) (a := (0:ℝ)) (b := x) (fun y _ => h y)
    (hg.intervalIntegrable _ _)
  rw [hFTC]; ring

/-- **Weak regularity.**  Every weak (integrated-form) solution of `u'' = (q - z) u` with
continuous potential `q` is in fact a classical solution. -/
theorem isClassicalSolution_of_isWeakSolution {q : ℝ → ℂ} (hq : Continuous q) {z : ℂ}
    {u : ℝ → ℂ} (hu : IsWeakSolution q z u) : IsClassicalSolution q z u := by
  obtain ⟨v, hv, hu1, hu2⟩ := hu
  have hud : ∀ x, HasDerivAt u (v x) x := hasDerivAt_of_primitive_rep hv hu1
  have hucont : Continuous u := continuous_of_hasDerivAt hud
  have hcont : Continuous fun t => (q t - z) * u t := by fun_prop
  exact ⟨v, hud, hasDerivAt_of_primitive_rep hcont hu2⟩

/-- Every classical solution is a weak solution. -/
theorem isWeakSolution_of_isClassicalSolution {q : ℝ → ℂ} (hq : Continuous q) {z : ℂ}
    {u : ℝ → ℂ} (hu : IsClassicalSolution q z u) : IsWeakSolution q z u := by
  obtain ⟨v, hud, hvd⟩ := hu
  have hvcont : Continuous v := continuous_of_hasDerivAt hvd
  have hucont : Continuous u := continuous_of_hasDerivAt hud
  have hcont : Continuous fun t => (q t - z) * u t := by fun_prop
  exact ⟨v, hvcont, primitive_rep_of_hasDerivAt hvcont hud,
    primitive_rep_of_hasDerivAt hcont hvd⟩

/-- The deficiency space consists exactly of the square-integrable classical solutions of the
ODE: the a priori merely weak regularity of deficiency elements upgrades to genuine
differentiability, so the deficiency space is represented by honest ODE solutions. -/
theorem deficiencyRepresentsODE_of_weakRegularity (q : ℝ → ℂ) (hq : Continuous q) (z : ℂ) :
    deficiencySpace q z = odeSolutionSpace q z := by
  ext u
  exact ⟨fun ⟨hL2, hw⟩ => ⟨hL2, isClassicalSolution_of_isWeakSolution hq hw⟩,
    fun ⟨hL2, hc⟩ => ⟨hL2, isWeakSolution_of_isClassicalSolution hq hc⟩⟩

end Brockian.Weyl.DeficiencyODE

