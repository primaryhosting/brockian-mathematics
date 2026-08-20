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
noncomputable def berryCurvature (A₁ A₂ : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => A₂ t y) x - deriv (fun t => A₁ x t) y

/-- The (first) Chern number of the Berry connection `A = (A₁, A₂)`: the integral of the
Berry curvature over the Brillouin zone `[0, L] × [0, L]`, normalised by `2π`. -/
noncomputable def chernNumber (A₁ A₂ : ℝ → ℝ → ℝ) (L : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) * ∫ y in (0:ℝ)..L, ∫ x in (0:ℝ)..L, berryCurvature A₁ A₂ x y

/-- The Kubo (TKNN) Hall conductance of the band: the Chern number in units of `e² / h`. -/
noncomputable def hallConductance (e h : ℝ) (A₁ A₂ : ℝ → ℝ → ℝ) (L : ℝ) : ℝ :=
  (e ^ 2 / h) * chernNumber A₁ A₂ L

section Stokes

variable (A₁ A₂ D₁ D₂ : ℝ → ℝ → ℝ)

/-- Pointwise formula for the Berry curvature in terms of the given partial derivatives. -/
theorem berryCurvature_eq
    (hdx : ∀ x y : ℝ, HasDerivAt (fun t => A₂ t y) (D₂ x y) x)
    (hdy : ∀ x y : ℝ, HasDerivAt (fun t => A₁ x t) (D₁ x y) y) (x y : ℝ) :
    berryCurvature A₁ A₂ x y = D₂ x y - D₁ x y := by
  simp [berryCurvature, (hdx x y).deriv, (hdy x y).deriv]

/-- Fubini's theorem for a continuous function on the square `[0, L] × [0, L]`. -/
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
theorem integral_berryCurvature_eq_boundary (L : ℝ) (hL : 0 ≤ L)
    (hA₂ : Continuous fun p : ℝ × ℝ => A₂ p.1 p.2)
    (hD₁ : Continuous fun p : ℝ × ℝ => D₁ p.1 p.2)
    (hD₂ : Continuous fun p : ℝ × ℝ => D₂ p.1 p.2)
    (hdx : ∀ x y : ℝ, HasDerivAt (fun t => A₂ t y) (D₂ x y) x)
    (hdy : ∀ x y : ℝ, HasDerivAt (fun t => A₁ x t) (D₁ x y) y) :
    (∫ y in (0:ℝ)..L, ∫ x in (0:ℝ)..L, berryCurvature A₁ A₂ x y)
      = (∫ y in (0:ℝ)..L, (A₂ L y - A₂ 0 y)) - ∫ x in (0:ℝ)..L, (A₁ x L - A₁ x 0) := by
  have hD₂cont : ∀ y : ℝ, Continuous fun x : ℝ => D₂ x y := fun y =>
    hD₂.comp (continuous_id.prodMk continuous_const)
  have hD₁cont : ∀ y : ℝ, Continuous fun x : ℝ => D₁ x y := fun y =>
    hD₁.comp (continuous_id.prodMk continuous_const)
  have hD₁cont' : ∀ x : ℝ, Continuous fun y : ℝ => D₁ x y := fun x =>
    hD₁.comp (continuous_const.prodMk continuous_id)
  -- inner integral in `x`
  have hinner : ∀ y : ℝ, (∫ x in (0:ℝ)..L, berryCurvature A₁ A₂ x y)
      = (A₂ L y - A₂ 0 y) - ∫ x in (0:ℝ)..L, D₁ x y := by
    intro y
    have hcongr : (∫ x in (0:ℝ)..L, berryCurvature A₁ A₂ x y)
        = ∫ x in (0:ℝ)..L, (D₂ x y - D₁ x y) := by
      refine intervalIntegral.integral_congr ?_
      intro x _
      exact berryCurvature_eq A₁ A₂ D₁ D₂ hdx hdy x y
    rw [hcongr, intervalIntegral.integral_sub
      ((hD₂cont y).intervalIntegrable _ _) ((hD₁cont y).intervalIntegrable _ _)]
    congr 1
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hdx x y)
      ((hD₂cont y).intervalIntegrable _ _)
  rw [intervalIntegral.integral_congr (g := fun y => (A₂ L y - A₂ 0 y) - ∫ x in (0:ℝ)..L, D₁ x y)
    (fun y _ => hinner y)]
  have hbdry : Continuous fun y : ℝ => A₂ L y - A₂ 0 y := by
    exact (hA₂.comp (continuous_const.prodMk continuous_id)).sub
      (hA₂.comp (continuous_const.prodMk continuous_id))
  have hparam : Continuous fun y : ℝ => ∫ x in (0:ℝ)..L, D₁ x y := by
    have hc : Continuous (Function.uncurry fun y x : ℝ => D₁ x y) :=
      hD₁.comp (continuous_snd.prodMk continuous_fst)
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hc
      continuous_const
  rw [intervalIntegral.integral_sub (hbdry.intervalIntegrable _ _)
    (hparam.intervalIntegrable _ _)]
  congr 1
  rw [interval_integral_swap D₁ L hL hD₁]
  refine intervalIntegral.integral_congr ?_
  intro x _
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hdy x y)
    ((hD₁cont' x).intervalIntegrable _ _))

end Stokes

/-- **TKNN.** For a Berry connection on the Brillouin torus `[0, L] × [0, L]` whose gauge is
periodic in the second momentum direction and whose transition function in the first direction
has winding number `n` (i.e. `A₂(L, ·) - A₂(0, ·) = 2πn/L`), the Chern number equals `n`. -/
theorem chernNumber_eq_winding (L : ℝ) (n : ℤ) (hL : 0 < L)
    (A₁ A₂ D₁ D₂ : ℝ → ℝ → ℝ)
    (hA₂ : Continuous fun p : ℝ × ℝ => A₂ p.1 p.2)
    (hD₁ : Continuous fun p : ℝ × ℝ => D₁ p.1 p.2)
    (hD₂ : Continuous fun p : ℝ × ℝ => D₂ p.1 p.2)
    (hdx : ∀ x y : ℝ, HasDerivAt (fun t => A₂ t y) (D₂ x y) x)
    (hdy : ∀ x y : ℝ, HasDerivAt (fun t => A₁ x t) (D₁ x y) y)
    (hper : ∀ x : ℝ, A₁ x L = A₁ x 0)
    (hwind : ∀ y : ℝ, A₂ L y - A₂ 0 y = 2 * Real.pi * (n : ℝ) / L) :
    chernNumber A₁ A₂ L = (n : ℝ) := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hLne : L ≠ 0 := ne_of_gt hL
  rw [chernNumber, integral_berryCurvature_eq_boundary A₁ A₂ D₁ D₂ L hL.le hA₂ hD₁ hD₂ hdx hdy]
  have h1 : (∫ y in (0:ℝ)..L, (A₂ L y - A₂ 0 y)) = L * (2 * Real.pi * (n : ℝ) / L) := by
    rw [intervalIntegral.integral_congr (g := fun _ => 2 * Real.pi * (n : ℝ) / L)
      (fun y _ => hwind y)]
    simp
    ring
  have h2 : (∫ x in (0:ℝ)..L, (A₁ x L - A₁ x 0)) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ)) (fun x _ => by simp [hper x])]
    simp
  rw [h1, h2]
  field_simp
  ring

/-- **TKNN: the integer quantum Hall conductance is a Chern number times `e²/h`.**
For a band whose Berry connection on the Brillouin torus has transition function of winding
number `n`, the Kubo–TKNN Hall conductance equals `n · e²/h`. -/
theorem tknn_chern_hall (e h L : ℝ) (n : ℤ) (hL : 0 < L)
    (A₁ A₂ D₁ D₂ : ℝ → ℝ → ℝ)
    (hA₂ : Continuous fun p : ℝ × ℝ => A₂ p.1 p.2)
    (hD₁ : Continuous fun p : ℝ × ℝ => D₁ p.1 p.2)
    (hD₂ : Continuous fun p : ℝ × ℝ => D₂ p.1 p.2)
    (hdx : ∀ x y : ℝ, HasDerivAt (fun t => A₂ t y) (D₂ x y) x)
    (hdy : ∀ x y : ℝ, HasDerivAt (fun t => A₁ x t) (D₁ x y) y)
    (hper : ∀ x : ℝ, A₁ x L = A₁ x 0)
    (hwind : ∀ y : ℝ, A₂ L y - A₂ 0 y = 2 * Real.pi * (n : ℝ) / L) :
    hallConductance e h A₁ A₂ L = (n : ℝ) * (e ^ 2 / h) := by
  rw [hallConductance,
    chernNumber_eq_winding L n hL A₁ A₂ D₁ D₂ hA₂ hD₁ hD₂ hdx hdy hper hwind, mul_comm]

/-- A concrete model (Landau gauge, uniform Berry curvature `2πn/L²` over the Brillouin zone)
satisfying all hypotheses of `Frontier.tknn_chern_hall`: its Hall conductance is `n · e²/h`. -/
theorem tknn_chern_hall_uniform (e h L : ℝ) (n : ℤ) (hL : 0 < L) :
    hallConductance e h (fun _ _ => 0) (fun x _ => 2 * Real.pi * (n : ℝ) * x / L ^ 2) L
      = (n : ℝ) * (e ^ 2 / h) := by
  have hLne : L ≠ 0 := ne_of_gt hL
  refine tknn_chern_hall e h L n hL _ _ (fun _ _ => 0)
    (fun _ _ => 2 * Real.pi * (n : ℝ) / L ^ 2) ?_ ?_ ?_ ?_ ?_ (fun _ => rfl) ?_
  · exact (continuous_const.mul continuous_fst).div_const _
  · exact continuous_const
  · exact continuous_const
  · intro x y
    simpa using ((hasDerivAt_id x).const_mul (2 * Real.pi * (n : ℝ))).div_const (L ^ 2)
  · intro x y
    simpa using (hasDerivAt_const y (0:ℝ))
  · intro y
    field_simp
    ring

end Frontier

