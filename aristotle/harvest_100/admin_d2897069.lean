/-
# Berry Phase Quantized
Category: Frontier Physics
Target: Frontier.berry_phase_quantized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Classical

open Set MeasureTheory

namespace Frontier

/-- The **Berry connection** is modelled as a real one-form on a two-dimensional parameter
space, i.e. a map `A : ℝ × ℝ → ℝ × ℝ` whose value `A p = (A₁ p, A₂ p)` gives the components
of the form `A₁ dx + A₂ dy` at the parameter point `p`. -/
abbrev BerryConnection := ℝ × ℝ → ℝ × ℝ

/-- The **Berry curvature** of a Berry connection `A` at a parameter point `p`:
`F = ∂₁ A₂ - ∂₂ A₁`, the exterior derivative of the connection one-form. -/
noncomputable def berryCurvature (A : BerryConnection) (p : ℝ × ℝ) : ℝ :=
  (fderiv ℝ (fun q => (A q).2) p) (1, 0) - (fderiv ℝ (fun q => (A q).1) p) (0, 1)

/-- The **Berry phase** accumulated along the closed loop that traverses, counterclockwise,
the boundary of the rectangle with corners `(a₁, a₂)` and `(b₁, b₂)`: it is the line integral
`∮ (A₁ dx + A₂ dy)` of the Berry connection along that loop. -/
noncomputable def berryPhase (A : BerryConnection) (a₁ a₂ b₁ b₂ : ℝ) : ℝ :=
  ((∫ x in a₁..b₁, (A (x, a₂)).1) + ∫ y in a₂..b₂, (A (b₁, y)).2) -
    ((∫ x in a₁..b₁, (A (x, b₂)).1) + ∫ y in a₂..b₂, (A (a₁, y)).2)

/-- The **Berry flux**: the integral of the Berry curvature over the rectangle with corners
`(a₁, a₂)` and `(b₁, b₂)`. -/
noncomputable def berryFlux (A : BerryConnection) (a₁ a₂ b₁ b₂ : ℝ) : ℝ :=
  ∫ x in a₁..b₁, ∫ y in a₂..b₂, berryCurvature A (x, y)

/-- **Berry phase = integral of the Berry curvature.**  For a differentiable Berry connection
whose curvature is integrable on the rectangle, the Berry phase around the (counterclockwise)
boundary loop of the rectangle equals the flux of the Berry curvature through it. -/
theorem berryPhase_eq_berryFlux (A : BerryConnection) (a₁ a₂ b₁ b₂ : ℝ)
    (h1 : Differentiable ℝ (fun q => (A q).1))
    (h2 : Differentiable ℝ (fun q => (A q).2))
    (Hi : IntegrableOn (berryCurvature A) (uIcc a₁ b₁ ×ˢ uIcc a₂ b₂)) :
    berryPhase A a₁ a₂ b₁ b₂ = berryFlux A a₁ a₂ b₁ b₂ := by
  have key := MeasureTheory.integral2_divergence_prod_of_hasFDerivAt
    (E := ℝ) (fun q => (A q).2) (fun q => -(A q).1)
    (fun p => fderiv ℝ (fun q => (A q).2) p) (fun p => -fderiv ℝ (fun q => (A q).1) p)
    a₁ a₂ b₁ b₂
    (h2.continuous.continuousOn) ((h1.continuous.neg).continuousOn)
    (fun x _ => (h2 x).hasFDerivAt)
    (fun x _ => ((h1 x).hasFDerivAt).neg)
    (by
      refine Hi.congr_fun ?_ (measurableSet_uIcc.prod measurableSet_uIcc)
      intro p _
      simp [berryCurvature, sub_eq_add_neg])
  simp only [ContinuousLinearMap.neg_apply] at key
  rw [berryPhase, berryFlux]
  rw [show (fun (x : ℝ) => ∫ y in a₂..b₂, berryCurvature A (x, y)) =
      fun (x : ℝ) => ∫ y in a₂..b₂,
        (fderiv ℝ (fun q => (A q).2) (x, y)) (1, 0) -
          (fderiv ℝ (fun q => (A q).1) (x, y)) (0, 1) from rfl]
  simp only [sub_eq_add_neg] at key ⊢
  rw [key]
  simp only [intervalIntegral.integral_neg]
  ring

/-- **Berry phase quantization.**  If the flux of the Berry curvature through the rectangle is
an integer multiple of `2π` — the quantization condition — then the Berry phase accumulated
around the boundary loop is that same integer multiple of `2π`. -/
theorem berry_phase_quantized (A : BerryConnection) (a₁ a₂ b₁ b₂ : ℝ) (n : ℤ)
    (h1 : Differentiable ℝ (fun q => (A q).1))
    (h2 : Differentiable ℝ (fun q => (A q).2))
    (Hi : IntegrableOn (berryCurvature A) (uIcc a₁ b₁ ×ˢ uIcc a₂ b₂))
    (hflux : berryFlux A a₁ a₂ b₁ b₂ = 2 * Real.pi * n) :
    berryPhase A a₁ a₂ b₁ b₂ = 2 * Real.pi * n := by
  rw [berryPhase_eq_berryFlux A a₁ a₂ b₁ b₂ h1 h2 Hi, hflux]

/-! ### A concrete instance: the symmetric gauge with one flux quantum -/

/-- The symmetric-gauge Berry connection `A = (k/2) (-y dx + x dy)`, whose Berry curvature is
the constant `k`. -/
noncomputable def symGauge (k : ℝ) : BerryConnection := fun p => (-(k / 2) * p.2, (k / 2) * p.1)

theorem symGauge_curvature (k : ℝ) (p : ℝ × ℝ) : berryCurvature (symGauge k) p = k := by
  have h2 : HasFDerivAt (fun q : ℝ × ℝ => ((symGauge k) q).2)
      ((k / 2) • (ContinuousLinearMap.fst ℝ ℝ ℝ)) p :=
    ((ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt).const_mul (k / 2)
  have h1 : HasFDerivAt (fun q : ℝ × ℝ => ((symGauge k) q).1)
      ((-(k / 2)) • (ContinuousLinearMap.snd ℝ ℝ ℝ)) p :=
    ((ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt).const_mul (-(k / 2))
  rw [berryCurvature, h1.fderiv, h2.fderiv]
  simp

theorem symGauge_differentiable_fst (k : ℝ) :
    Differentiable ℝ (fun q : ℝ × ℝ => ((symGauge k) q).1) := by
  exact fun p => (((ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt).const_mul
    (-(k / 2))).differentiableAt

theorem symGauge_differentiable_snd (k : ℝ) :
    Differentiable ℝ (fun q : ℝ × ℝ => ((symGauge k) q).2) := by
  exact fun p => (((ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt).const_mul
    (k / 2)).differentiableAt

/-- With one quantum of flux (`k = 2π` through the unit square), both the Berry flux and the
Berry phase equal `2π`; in particular the hypotheses of `berry_phase_quantized` are satisfiable
non-vacuously. -/
theorem symGauge_berry_phase_two_pi :
    berryFlux (symGauge (2 * Real.pi)) 0 0 1 1 = 2 * Real.pi ∧
      berryPhase (symGauge (2 * Real.pi)) 0 0 1 1 = 2 * Real.pi := by
  have hflux : berryFlux (symGauge (2 * Real.pi)) 0 0 1 1 = 2 * Real.pi := by
    simp [berryFlux, symGauge_curvature]
  refine ⟨hflux, ?_⟩
  have hint : IntegrableOn (berryCurvature (symGauge (2 * Real.pi)))
      (uIcc (0 : ℝ) 1 ×ˢ uIcc (0 : ℝ) 1) := by
    have hconst : IntegrableOn (fun _ : ℝ × ℝ => 2 * Real.pi)
        (uIcc (0 : ℝ) 1 ×ˢ uIcc (0 : ℝ) 1) := by
      refine MeasureTheory.integrableOn_const (C := 2 * Real.pi) ?_ ?_
      · rw [MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod]
        simp [Real.volume_Icc, uIcc_of_le]
      · simp [enorm_mul, ENNReal.mul_eq_top]
    exact hconst.congr_fun (fun p _ => (symGauge_curvature _ p).symm)
      (measurableSet_uIcc.prod measurableSet_uIcc)
  have h := berry_phase_quantized (symGauge (2 * Real.pi)) 0 0 1 1 1
    (symGauge_differentiable_fst _) (symGauge_differentiable_snd _) hint
    (by rw [hflux]; push_cast; ring)
  simpa using h

/-- **Quantization, subgroup form.**  If the Berry flux lies in the subgroup `2π ℤ` of `ℝ`,
then so does the Berry phase around the closed boundary loop. -/
theorem berryPhase_mem_zmultiples_two_pi (A : BerryConnection) (a₁ a₂ b₁ b₂ : ℝ)
    (h1 : Differentiable ℝ (fun q => (A q).1))
    (h2 : Differentiable ℝ (fun q => (A q).2))
    (Hi : IntegrableOn (berryCurvature A) (uIcc a₁ b₁ ×ˢ uIcc a₂ b₂))
    (hflux : berryFlux A a₁ a₂ b₁ b₂ ∈ AddSubgroup.zmultiples (2 * Real.pi)) :
    berryPhase A a₁ a₂ b₁ b₂ ∈ AddSubgroup.zmultiples (2 * Real.pi) := by
  rw [berryPhase_eq_berryFlux A a₁ a₂ b₁ b₂ h1 h2 Hi]
  exact hflux

/-! ### The quantum-mechanical Berry phase of a cyclic family of states -/

/-- The Berry phase `i ∮ ⟨ψ | ∂ₜ ψ⟩ dt` accumulated over the time interval `[0, T]` by a
(normalized) family of states `ψ : ℝ → ℂ` in a one-dimensional Hilbert space. -/
noncomputable def stateBerryPhase (psi : ℝ → ℂ) (T : ℝ) : ℂ :=
  Complex.I * ∫ t in (0 : ℝ)..T, (starRingEnd ℂ) (psi t) * deriv psi t

/-- **The Berry phase of a winding family of states is quantized.**  For the cyclic family
`ψₙ(t) = exp(i n t)` of unit vectors, which returns to itself at `t = 2π`, the Berry phase is
`-2π n`, an integer multiple of `2π`. -/
theorem stateBerryPhase_winding (n : ℤ) :
    stateBerryPhase (fun t => Complex.exp ((n : ℂ) * (t : ℂ) * Complex.I)) (2 * Real.pi)
      = -(2 * Real.pi * n) := by
  have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Complex.exp ((n : ℂ) * (t : ℂ) * Complex.I))
      (Complex.exp ((n : ℂ) * (t : ℂ) * Complex.I) * ((n : ℂ) * Complex.I)) t := by
    intro t
    have h0 : HasDerivAt (fun t : ℝ => ((n : ℂ) * (t : ℂ) * Complex.I))
        ((n : ℂ) * Complex.I) t := by
      have hre : HasDerivAt (fun t : ℝ => ((t : ℂ))) 1 t := Complex.ofRealCLM.hasDerivAt
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        ((hre.const_mul ((n : ℂ))).mul_const Complex.I)
    simpa using h0.cexp
  have hint : ∀ t : ℝ,
      (starRingEnd ℂ) (Complex.exp ((n : ℂ) * (t : ℂ) * Complex.I)) *
        deriv (fun t : ℝ => Complex.exp ((n : ℂ) * (t : ℂ) * Complex.I)) t
        = (n : ℂ) * Complex.I := by
    intro t
    rw [(hd t).deriv, ← Complex.exp_conj, ← mul_assoc, ← Complex.exp_add]
    have hz : (starRingEnd ℂ) ((n : ℂ) * (t : ℂ) * Complex.I) +
        (n : ℂ) * (t : ℂ) * Complex.I = 0 := by
      simp
    rw [hz]
    simp
  rw [stateBerryPhase]
  simp only [hint]
  rw [intervalIntegral.integral_const]
  simp only [sub_zero, Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_ofNat]
  linear_combination (2 * (Real.pi : ℂ) * (n : ℂ)) * Complex.I_mul_I

/-- The Berry phase of the winding family `ψₙ(t) = exp(i n t)` is a real integer multiple
of `2π`. -/
theorem stateBerryPhase_winding_quantized (n : ℤ) :
    ∃ m : ℤ, stateBerryPhase (fun t => Complex.exp ((n : ℂ) * (t : ℂ) * Complex.I))
      (2 * Real.pi) = 2 * Real.pi * m := by
  refine ⟨-n, ?_⟩
  rw [stateBerryPhase_winding n]
  push_cast
  ring

end Frontier

