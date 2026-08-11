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

namespace Frontier

open MeasureTheory intervalIntegral

/-- The Berry curvature `F₁₂ = ∂₁A₂ - ∂₂A₁` of a Berry connection `A = (A₁, A₂)` on the
Brillouin zone, given the two partial derivatives `d1A2 = ∂₁A₂` and `d2A1 = ∂₂A₁`. -/
def berryCurvature (d1A2 d2A1 : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ := d1A2 x y - d2A1 x y

/-- The (first) Chern number of a Berry curvature `F` on the Brillouin zone `[0,1]²`:
`C = (1/2π) ∫∫ F`. -/
noncomputable def chernNumber (F : ℝ → ℝ → ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ * ∫ y in (0:ℝ)..1, ∫ x in (0:ℝ)..1, F x y

/-- The zero-temperature Hall conductance of a filled band, as given by the Kubo formula:
`σ_xy = (e²/(2π h)) ∫∫ F` where `F` is the Berry curvature of the band. -/
noncomputable def hallConductance (F : ℝ → ℝ → ℝ) (e h : ℝ) : ℝ :=
  e ^ 2 / (2 * Real.pi * h) * ∫ y in (0:ℝ)..1, ∫ x in (0:ℝ)..1, F x y

/-- A continuous function of two variables is integrable on the unit square (for the product
of the measures restricted to `Set.Ioc 0 1`). -/
lemma integrable_uncurry_of_continuous {g : ℝ → ℝ → ℝ}
    (hg : Continuous fun p : ℝ × ℝ => g p.1 p.2) :
    Integrable (Function.uncurry g)
      (((volume.restrict (Set.Ioc (0:ℝ) 1))).prod (volume.restrict (Set.Ioc (0:ℝ) 1))) := by
  rw [Measure.prod_restrict]
  have hcpt : IsCompact ((Set.Icc (0:ℝ) 1) ×ˢ (Set.Icc (0:ℝ) 1)) :=
    (isCompact_Icc).prod isCompact_Icc
  have h1 : IntegrableOn (Function.uncurry g) ((Set.Icc (0:ℝ) 1) ×ˢ (Set.Icc (0:ℝ) 1)) volume := by
    exact (hg.continuousOn).integrableOn_compact hcpt
  exact h1.mono_set (Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self)

/-- Fubini on the unit square for continuous integrands. -/
lemma integral_square_swap {g : ℝ → ℝ → ℝ}
    (hg : Continuous fun p : ℝ × ℝ => g p.1 p.2) :
    (∫ y in (0:ℝ)..1, ∫ x in (0:ℝ)..1, g x y)
      = ∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1, g x y := by
  have h01 : (0:ℝ) ≤ 1 := zero_le_one
  simp_rw [intervalIntegral.integral_of_le h01]
  exact (MeasureTheory.integral_integral_swap
    (integrable_uncurry_of_continuous hg)).symm

/-- Integrating `∂₁A₂` over the Brillouin zone: only the winding of `A₂` in the `k₁`
direction survives. -/
lemma integral_d1A2 {A2 d1A2 : ℝ → ℝ → ℝ}
    (hd1 : ∀ x y : ℝ, HasDerivAt (fun t : ℝ => A2 t y) (d1A2 x y) x)
    (hc1 : Continuous fun p : ℝ × ℝ => d1A2 p.1 p.2) (y : ℝ) :
    (∫ x in (0:ℝ)..1, d1A2 x y) = A2 1 y - A2 0 y := by
  have hcont : Continuous fun x : ℝ => d1A2 x y :=
    hc1.comp (continuous_id.prodMk continuous_const)
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd1 x y)
    (hcont.intervalIntegrable 0 1)

/-- Integrating `∂₂A₁` over the Brillouin zone: it vanishes when `A₁` is periodic in `k₂`. -/
lemma integral_d2A1_eq_zero {A1 d2A1 : ℝ → ℝ → ℝ}
    (hd2 : ∀ x y : ℝ, HasDerivAt (fun t : ℝ => A1 x t) (d2A1 x y) y)
    (hc2 : Continuous fun p : ℝ × ℝ => d2A1 p.1 p.2)
    (hper : ∀ x : ℝ, A1 x 1 = A1 x 0) :
    (∫ y in (0:ℝ)..1, ∫ x in (0:ℝ)..1, d2A1 x y) = 0 := by
  rw [integral_square_swap hc2]
  have : ∀ x : ℝ, (∫ y in (0:ℝ)..1, d2A1 x y) = 0 := by
    intro x
    have hcont : Continuous fun y : ℝ => d2A1 x y :=
      hc2.comp (continuous_const.prodMk continuous_id)
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t : ℝ => A1 x t)
      (f' := fun y : ℝ => d2A1 x y) (fun y _ => hd2 x y) (hcont.intervalIntegrable 0 1)
    rw [this]
    simp [hper x]
  simp [this]

/-- **TKNN (base case).** For a Berry connection `A = (A₁, A₂)` on the Brillouin zone torus
`[0,1]²` whose gauge is periodic in `k₂` and whose transition function in the `k₁` direction
has winding number `n` (i.e. `A₂(1, k₂) = A₂(0, k₂) + 2πn`), the Chern number of the Berry
curvature `F₁₂ = ∂₁A₂ - ∂₂A₁` is the integer `n`, and consequently the Hall conductance given
by the Kubo formula is quantized:  `σ_xy = n · e²/h`. -/
theorem tknn_chern_hall
    {A1 A2 d1A2 d2A1 : ℝ → ℝ → ℝ} {n : ℤ} (e h : ℝ)
    (hd1 : ∀ x y : ℝ, HasDerivAt (fun t : ℝ => A2 t y) (d1A2 x y) x)
    (hd2 : ∀ x y : ℝ, HasDerivAt (fun t : ℝ => A1 x t) (d2A1 x y) y)
    (hc1 : Continuous fun p : ℝ × ℝ => d1A2 p.1 p.2)
    (hc2 : Continuous fun p : ℝ × ℝ => d2A1 p.1 p.2)
    (hper : ∀ x : ℝ, A1 x 1 = A1 x 0)
    (hwind : ∀ y : ℝ, A2 1 y = A2 0 y + 2 * Real.pi * (n : ℝ)) :
    chernNumber (berryCurvature d1A2 d2A1) = (n : ℝ) ∧
      hallConductance (berryCurvature d1A2 d2A1) e h = (n : ℝ) * (e ^ 2 / h) := by
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  -- the total curvature is `2πn`
  have hint : (∫ y in (0:ℝ)..1, ∫ x in (0:ℝ)..1, berryCurvature d1A2 d2A1 x y)
      = 2 * Real.pi * (n : ℝ) := by
    have hsplit : ∀ y : ℝ, (∫ x in (0:ℝ)..1, berryCurvature d1A2 d2A1 x y)
        = (∫ x in (0:ℝ)..1, d1A2 x y) - ∫ x in (0:ℝ)..1, d2A1 x y := by
      intro y
      have h1 : Continuous fun x : ℝ => d1A2 x y :=
        hc1.comp (continuous_id.prodMk continuous_const)
      have h2 : Continuous fun x : ℝ => d2A1 x y :=
        hc2.comp (continuous_id.prodMk continuous_const)
      simpa [berryCurvature] using
        intervalIntegral.integral_sub (h1.intervalIntegrable 0 1) (h2.intervalIntegrable 0 1)
    have hA2 : ∀ y : ℝ, (∫ x in (0:ℝ)..1, d1A2 x y) = 2 * Real.pi * (n : ℝ) := by
      intro y
      rw [integral_d1A2 hd1 hc1 y, hwind y]; ring
    have hfun : (fun y : ℝ => ∫ x in (0:ℝ)..1, berryCurvature d1A2 d2A1 x y)
        = fun y : ℝ => 2 * Real.pi * (n : ℝ) - ∫ x in (0:ℝ)..1, d2A1 x y := by
      funext y; rw [hsplit y, hA2 y]
    rw [hfun]
    have hcontd2 : Continuous fun y : ℝ => ∫ x in (0:ℝ)..1, d2A1 x y := by
      have : Continuous fun y : ℝ => ∫ x in (0:ℝ)..1, d2A1 x y := by
        apply continuous_parametric_intervalIntegral_of_continuous
        · exact hc2.comp (continuous_snd.prodMk continuous_fst)
        · exact continuous_const
      exact this
    rw [intervalIntegral.integral_sub (_root_.intervalIntegrable_const)
      (hcontd2.intervalIntegrable 0 1), integral_d2A1_eq_zero hd2 hc2 hper]
    simp
  constructor
  · rw [chernNumber, hint]
    field_simp
  · rw [hallConductance, hint]
    rcases eq_or_ne h 0 with rfl | hh
    · simp
    · field_simp

/-- The hypotheses of `Frontier.tknn_chern_hall` are non-vacuous: the Landau-type gauge
`A₁ = 0`, `A₂(k₁, k₂) = 2π n k₁` has constant Berry curvature `2π n`, Chern number `n`,
and Hall conductance `n · e²/h`. -/
theorem tknn_chern_hall_landau_gauge (n : ℤ) (e h : ℝ) :
    chernNumber (berryCurvature (fun _ _ => 2 * Real.pi * (n : ℝ)) (fun _ _ => 0)) = (n : ℝ) ∧
      hallConductance (berryCurvature (fun _ _ => 2 * Real.pi * (n : ℝ)) (fun _ _ => 0)) e h
        = (n : ℝ) * (e ^ 2 / h) := by
  refine tknn_chern_hall (A1 := fun _ _ => 0) (A2 := fun x _ => 2 * Real.pi * (n : ℝ) * x)
    (n := n) e h ?_ ?_ ?_ ?_ ?_ ?_
  · intro x y
    simpa using (hasDerivAt_id x).const_mul (2 * Real.pi * (n : ℝ))
  · intro x y
    simpa using (hasDerivAt_const y (0 : ℝ))
  · exact continuous_const
  · exact continuous_const
  · intro x; rfl
  · intro y; ring

end Frontier

