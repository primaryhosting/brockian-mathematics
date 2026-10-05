/-
# Lieb Thirring Stability
Category: Frontier Physics
Target: Frontier.lieb_thirring_stability
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above is a plain block comment rather than a `/-!` module
-- docstring only because Lean 4 requires `import` to precede any docstring;
-- the identical module docstring is reproduced immediately after the imports.)

import Mathlib

/-!
# Lieb Thirring Stability
Category: Frontier Physics
Target: Frontier.lieb_thirring_stability
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

/-!
## Overview

The Lieb–Thirring route to the *stability of matter* combines three ingredients:

1. **The Lieb–Thirring kinetic energy inequality.**  For a normalized fermionic
   wave function `Ψ` of `N` particles with one-particle density `ρ`, the kinetic
   energy obeys `T ≥ K_LT * ∫ ρ^(5/3)`.

2. **An electrostatic (Baxter / Lieb–Yau type) inequality.**  The full Coulomb
   interaction of electrons and nuclei is bounded below by a purely local term,
   `V ≥ - C_ES * ∫ ρ^(4/3) - C_nuc`, where `C_nuc` collects the nucleus-dependent
   contribution (proportional to the number of nuclei).

3. **A functional-analytic interpolation step**, which turns the competition
   between the two local terms into a bound that is *linear in the particle
   number* `N = ∫ ρ`.

Step 3 is the mathematical heart of the reduction, and it is what is proved here
from scratch: by Cauchy–Schwarz (the `p = q = 2` case of Hölder's inequality)

  `∫ ρ^(4/3) = ∫ ρ^(1/2) · ρ^(5/6) ≤ (∫ ρ)^(1/2) · (∫ ρ^(5/3))^(1/2)`,

so that with `t = ∫ ρ^(5/3)` and `N = ∫ ρ`,

  `T + V ≥ K_LT * t - C_ES * √N * √t - C_nuc ≥ - (C_ES^2 / (4 K_LT)) * N - C_nuc`

by the arithmetic–geometric mean inequality.  The conclusion is exactly
*stability of the second kind*: the energy per particle is bounded below by a
constant that does not depend on `N`.

Everything below is stated for an arbitrary measure space, so that it applies
verbatim to `ρ : ℝ³ → ℝ≥0∞` with Lebesgue measure.  Densities are taken to be
`ℝ≥0∞`-valued so that all the integrals are unconditionally defined; the two
physical input inequalities (1) and (2) enter as hypotheses, and the deduction of
stability from them is fully verified.
-/

namespace Frontier

open MeasureTheory ENNReal

section Densities

variable {α : Type*} [MeasurableSpace α]

/-- The total mass (particle number) `∫ ρ` of a one-particle density `ρ`. -/
noncomputable def particleNumber (μ : Measure α) (ρ : α → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ x, ρ x ∂μ

/-- The Lieb–Thirring density functional `∫ ρ^(5/3)`, the right-hand side of the
Lieb–Thirring kinetic energy inequality. -/
noncomputable def ltKineticFunctional (μ : Measure α) (ρ : α → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ x, ρ x ^ (5 / 3 : ℝ) ∂μ

/-- The local electrostatic functional `∫ ρ^(4/3)` appearing in the Baxter /
Lieb–Yau electrostatic inequality. -/
noncomputable def coulombFunctional (μ : Measure α) (ρ : α → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ x, ρ x ^ (4 / 3 : ℝ) ∂μ

end Densities

/-!
### The interpolation inequality `∫ ρ^(4/3) ≤ (∫ ρ)^(1/2) (∫ ρ^(5/3))^(1/2)`
-/

/-- **Interpolation between the electrostatic and the Lieb–Thirring functional.**
Cauchy–Schwarz applied to the splitting `ρ^(4/3) = ρ^(1/2) · ρ^(5/6)` gives
`∫ ρ^(4/3) ≤ (∫ ρ)^(1/2) · (∫ ρ^(5/3))^(1/2)`. -/
theorem coulombFunctional_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α} (ρ : α → ℝ≥0∞)
    (hρ : AEMeasurable ρ μ) :
    coulombFunctional μ ρ ≤
      particleNumber μ ρ ^ (1 / 2 : ℝ) * ltKineticFunctional μ ρ ^ (1 / 2 : ℝ) := by
  have hconj : (2 : ℝ).HolderConjugate 2 := by constructor <;> norm_num
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hconj
    (f := fun x => ρ x ^ (1 / 2 : ℝ)) (g := fun x => ρ x ^ (5 / 6 : ℝ))
    (hρ.pow_const _) (hρ.pow_const _)
  simp only [Pi.mul_apply] at h
  unfold coulombFunctional particleNumber ltKineticFunctional
  calc ∫⁻ x, ρ x ^ (4 / 3 : ℝ) ∂μ
      = ∫⁻ x, ρ x ^ (1 / 2 : ℝ) * ρ x ^ (5 / 6 : ℝ) ∂μ := by
        refine lintegral_congr fun x => ?_
        rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
        norm_num
    _ ≤ _ := by
        refine h.trans_eq ?_
        congr 1
        · congr 1
          refine lintegral_congr fun x => ?_
          rw [← ENNReal.rpow_mul]
          norm_num
        · congr 1
          refine lintegral_congr fun x => ?_
          rw [← ENNReal.rpow_mul]
          norm_num

/-- Real-valued form of the interpolation inequality: if the particle number and
the Lieb–Thirring functional are the finite quantities `N` and `t`, then
`∫ ρ^(4/3) ≤ √N * √t`. -/
theorem coulombFunctional_toReal_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α} (ρ : α → ℝ≥0∞)
    (hρ : AEMeasurable ρ μ) {N t : ℝ} (hN : 0 ≤ N) (ht : 0 ≤ t)
    (hmass : particleNumber μ ρ = ENNReal.ofReal N)
    (hkin : ltKineticFunctional μ ρ = ENNReal.ofReal t) :
    (coulombFunctional μ ρ).toReal ≤ Real.sqrt N * Real.sqrt t := by
  have hle := coulombFunctional_le ρ hρ
  rw [hmass, hkin] at hle
  have hfin : (ENNReal.ofReal N) ^ (1 / 2 : ℝ) * (ENNReal.ofReal t) ^ (1 / 2 : ℝ) ≠ ⊤ := by
    refine ENNReal.mul_ne_top ?_ ?_ <;>
      exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) (by simp)
  have h1 : (coulombFunctional μ ρ).toReal ≤
      ((ENNReal.ofReal N) ^ (1 / 2 : ℝ) * (ENNReal.ofReal t) ^ (1 / 2 : ℝ)).toReal :=
    ENNReal.toReal_le_toReal (ne_top_of_le_ne_top hfin hle) hfin |>.mpr hle
  refine h1.trans_eq ?_
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal hN, ENNReal.toReal_ofReal ht, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]

/-!
### The arithmetic–geometric mean step
-/

/-- **The AM–GM step.**  For `K > 0` and `N, t ≥ 0` (any real `C`),
`K t - C √N √t ≥ - C^2 N / (4 K)`.  This is the completion of the square
`K t - C √N √t + C^2 N / (4K) = (2 K √t - C √N)^2 / (4K)`. -/
theorem kinetic_dominates_coulomb {K C N t : ℝ} (hK : 0 < K)
    (hN : 0 ≤ N) (ht : 0 ≤ t) :
    -(C ^ 2 / (4 * K)) * N ≤ K * t - C * (Real.sqrt N * Real.sqrt t) := by
  set m := Real.sqrt N with hm
  set s := Real.sqrt t with hs
  have hm2 : m ^ 2 = N := Real.sq_sqrt hN
  have hs2 : s ^ 2 = t := Real.sq_sqrt ht
  rw [← hm2, ← hs2]
  have hkey : K * s ^ 2 - C * (m * s) - -(C ^ 2 / (4 * K)) * m ^ 2
      = (2 * K * s - C * m) ^ 2 / (4 * K) := by
    field_simp
    ring
  have hnn : 0 ≤ (2 * K * s - C * m) ^ 2 / (4 * K) := by positivity
  linarith [hkey, hnn]

/-!
### Stability of matter
-/

/--
**Lieb–Thirring stability of matter (Lean-checked reduction).**

Let `ρ` be the one-particle density of a state of a Coulomb system on an
arbitrary measure space, with finite particle number `N = ∫ ρ` and finite
Lieb–Thirring functional `t = ∫ ρ^(5/3)`.

Assume the two physical input inequalities:

* the **Lieb–Thirring kinetic energy inequality** `K_LT * t ≤ T`, with
  `K_LT > 0`;
* the **electrostatic (Baxter / Lieb–Yau) inequality**
  `- C_ES * ∫ ρ^(4/3) - C_nuc ≤ V`, with `C_ES ≥ 0` and `C_nuc` the
  nucleus-dependent constant.

Then the total energy `E = T + V` satisfies

  `E ≥ - (C_ES^2 / (4 K_LT)) * N - C_nuc`,

i.e. it is bounded below by a constant times the particle number, plus the
nuclear contribution.  This is *stability of the second kind*.
-/
theorem lieb_thirring_stability
    {α : Type*} [MeasurableSpace α] {μ : Measure α} (ρ : α → ℝ≥0∞)
    (hρ : AEMeasurable ρ μ)
    {N t : ℝ} (hN : 0 ≤ N) (ht : 0 ≤ t)
    (hmass : particleNumber μ ρ = ENNReal.ofReal N)
    (hkin : ltKineticFunctional μ ρ = ENNReal.ofReal t)
    {K_LT C_ES C_nuc T V E : ℝ} (hK : 0 < K_LT) (hC : 0 ≤ C_ES)
    (hLT : K_LT * t ≤ T)
    (hES : -(C_ES * (coulombFunctional μ ρ).toReal) - C_nuc ≤ V)
    (hE : E = T + V) :
    -(C_ES ^ 2 / (4 * K_LT)) * N - C_nuc ≤ E := by
  have hcs : (coulombFunctional μ ρ).toReal ≤ Real.sqrt N * Real.sqrt t :=
    coulombFunctional_toReal_le ρ hρ hN ht hmass hkin
  have hamgm : -(C_ES ^ 2 / (4 * K_LT)) * N ≤ K_LT * t - C_ES * (Real.sqrt N * Real.sqrt t) :=
    kinetic_dominates_coulomb hK hN ht
  have hmul : C_ES * (coulombFunctional μ ρ).toReal ≤ C_ES * (Real.sqrt N * Real.sqrt t) :=
    mul_le_mul_of_nonneg_left hcs hC
  rw [hE]
  linarith

/--
**Stability of the second kind, in the usual form.**

If in addition the nuclear constant is proportional to the number `M` of nuclei,
`C_nuc = c_nuc * M`, then the energy obeys a bound of the form
`E ≥ - c * (N + M)` with `c` independent of `N` and `M`.
-/
theorem stability_of_second_kind
    {α : Type*} [MeasurableSpace α] {μ : Measure α} (ρ : α → ℝ≥0∞)
    (hρ : AEMeasurable ρ μ)
    {N t : ℝ} (hN : 0 ≤ N) (ht : 0 ≤ t)
    (hmass : particleNumber μ ρ = ENNReal.ofReal N)
    (hkin : ltKineticFunctional μ ρ = ENNReal.ofReal t)
    {K_LT C_ES c_nuc M T V E : ℝ} (hK : 0 < K_LT) (hC : 0 ≤ C_ES)
    (hM : 0 ≤ M)
    (hLT : K_LT * t ≤ T)
    (hES : -(C_ES * (coulombFunctional μ ρ).toReal) - c_nuc * M ≤ V)
    (hE : E = T + V) :
    -(max (C_ES ^ 2 / (4 * K_LT)) c_nuc) * (N + M) ≤ E := by
  have h := lieb_thirring_stability ρ hρ hN ht hmass hkin (K_LT := K_LT) (C_ES := C_ES)
    (C_nuc := c_nuc * M) hK hC hLT hES hE
  set c := max (C_ES ^ 2 / (4 * K_LT)) c_nuc with hcdef
  have h1 : C_ES ^ 2 / (4 * K_LT) ≤ c := le_max_left _ _
  have h2 : c_nuc ≤ c := le_max_right _ _
  have hb1 : C_ES ^ 2 / (4 * K_LT) * N ≤ c * N := by nlinarith
  have hb2 : c_nuc * M ≤ c * M := by nlinarith
  nlinarith [h, hb1, hb2]

/-!
### Non-vacuity

The hypotheses of `lieb_thirring_stability` are satisfiable: a concrete density
on a one-point measure space, together with concrete energies, realises them.
-/

/-- A concrete instance showing the hypotheses of `lieb_thirring_stability` are
consistent (a unit density on a one-point space, with `N = t = ∫ ρ^(4/3) = 1`). -/
theorem stability_hypotheses_satisfiable :
    ∃ (μ : Measure Unit) (ρ : Unit → ℝ≥0∞),
      AEMeasurable ρ μ ∧
      particleNumber μ ρ = ENNReal.ofReal 1 ∧
      ltKineticFunctional μ ρ = ENNReal.ofReal 1 ∧
      (coulombFunctional μ ρ).toReal = 1 := by
  refine ⟨Measure.dirac (), fun _ => 1, aemeasurable_const, ?_, ?_, ?_⟩ <;>
    simp [particleNumber, ltKineticFunctional, coulombFunctional]

/-!
## The one-dimensional base case

The reduction above takes the Lieb–Thirring kinetic inequality as an input.  In
one space dimension the corresponding *ground state* bound can be proved outright,
and that is done here from scratch.

For a Schrödinger operator `-d²/dx² + V` on the line with a non-positive potential
`V ∈ L¹`, every normalized state `ψ` satisfies

  `∫ |ψ'|² + ∫ V |ψ|² ≥ - (∫ |V|)²`.

This is the `γ = 1/2`, `d = 1` Lieb–Thirring bound for the lowest eigenvalue (with
the constant `1` in place of the sharp constant `1/4`).  The proof has exactly the
same shape as the reduction above: a Sobolev-type sup bound plays the role of the
interpolation inequality, and the conclusion follows by completing a square.
-/

section OneDimensional

open Filter

/-- **Cauchy–Schwarz for real integrals.**  For `f, g ∈ L²(ℝ)`,
`∫ |f| |g| ≤ (∫ f²)^(1/2) (∫ g²)^(1/2)`. -/
theorem integral_abs_mul_le_sqrt_mul_sqrt {f g : ℝ → ℝ}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    ∫ x, |f x| * |g x| ≤ Real.sqrt (∫ x, f x ^ 2) * Real.sqrt (∫ x, g x ^ 2) := by
  have hconj : (2 : ℝ).HolderConjugate 2 := by constructor <;> norm_num
  have h2 : ENNReal.ofReal (2 : ℝ) = 2 := by simp [ENNReal.ofReal_ofNat]
  have h := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume) hconj
    (f := fun x => |f x|) (g := fun x => |g x|)
    (Filter.Eventually.of_forall fun x => abs_nonneg _)
    (Filter.Eventually.of_forall fun x => abs_nonneg _)
    (by rw [h2]; exact hf.abs) (by rw [h2]; exact hg.abs)
  refine h.trans_eq ?_
  have e1 : ∀ u : ℝ → ℝ, (∫ x, |u x| ^ (2 : ℝ)) = ∫ x, u x ^ 2 := by
    intro u
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
  rw [e1, e1, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]

/-- **Sobolev-type sup bound in one dimension.**  For a `C¹` function `ψ` with `ψ`
and `ψ'` in `L²(ℝ)` and `ψ → 0` at `-∞`,
`ψ(x)² ≤ 2 (∫ ψ²)^(1/2) (∫ (ψ')²)^(1/2)` for every `x`.

This is the one-dimensional analogue, for a single particle, of the Lieb–Thirring
interpolation step. -/
theorem sobolev_sup_bound_1d (ψ : ℝ → ℝ) (hψ : ContDiff ℝ 1 ψ)
    (hL2 : MemLp ψ 2 volume) (hL2' : MemLp (deriv ψ) 2 volume)
    (hdecay : Tendsto ψ atBot (nhds 0)) (x : ℝ) :
    ψ x ^ 2 ≤ 2 * Real.sqrt (∫ y, ψ y ^ 2) * Real.sqrt (∫ y, deriv ψ y ^ 2) := by
  have hB : Integrable (fun y => |ψ y| * |deriv ψ y|) volume :=
    MeasureTheory.MemLp.integrable_mul hL2.abs hL2'.abs
  set B := ∫ y, |ψ y| * |deriv ψ y| with hBdef
  have hcont : Continuous ψ := hψ.continuous
  have hcont' : Continuous (deriv ψ) := hψ.continuous_deriv le_rfl
  have key : ∀ a : ℝ, a ≤ x → ψ x ^ 2 ≤ ψ a ^ 2 + 2 * B := by
    intro a hax
    have hderiv : ∀ y ∈ Set.uIcc a x, HasDerivAt (fun z => ψ z ^ 2) (2 * ψ y * deriv ψ y) y := by
      intro y _
      have h1 : HasDerivAt ψ (deriv ψ y) y := (hψ.differentiable one_ne_zero y).hasDerivAt
      simpa [mul_comm, mul_assoc, mul_left_comm] using h1.pow 2
    have hint : IntervalIntegrable (fun y => 2 * ψ y * deriv ψ y) volume a x :=
      Continuous.intervalIntegrable (by fun_prop) a x
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    have hb : |∫ y in a..x, 2 * ψ y * deriv ψ y| ≤ 2 * B := by
      have h1 : |∫ y in a..x, 2 * ψ y * deriv ψ y| ≤ ∫ y in a..x, |2 * ψ y * deriv ψ y| := by
        rw [intervalIntegral.integral_of_le hax, intervalIntegral.integral_of_le hax]
        simpa [Real.norm_eq_abs] using
          norm_integral_le_integral_norm (μ := volume.restrict (Set.Ioc a x))
            (fun y => 2 * ψ y * deriv ψ y)
      refine h1.trans ?_
      rw [intervalIntegral.integral_of_le hax]
      have h2 : ∫ y in Set.Ioc a x, |2 * ψ y * deriv ψ y| ≤ ∫ y, |2 * ψ y * deriv ψ y| := by
        refine setIntegral_le_integral ?_ (Filter.Eventually.of_forall fun y => abs_nonneg _)
        simpa [abs_mul, mul_assoc] using (hB.const_mul 2).abs
      refine h2.trans_eq ?_
      simp only [abs_mul, abs_two]
      rw [hBdef, ← integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall fun y => by ring)
    have habs := abs_le.mp hb
    linarith [hFTC, habs.1, habs.2]
  have hlim : Tendsto (fun a => ψ a ^ 2 + 2 * B) atBot (nhds (0 ^ 2 + 2 * B)) :=
    (hdecay.pow 2).add tendsto_const_nhds
  have hfin : ψ x ^ 2 ≤ 0 ^ 2 + 2 * B := by
    refine ge_of_tendsto hlim ?_
    filter_upwards [Filter.eventually_le_atBot x] with a ha
    exact key a ha
  have hCS : B ≤ Real.sqrt (∫ y, ψ y ^ 2) * Real.sqrt (∫ y, deriv ψ y ^ 2) :=
    integral_abs_mul_le_sqrt_mul_sqrt hL2 hL2'
  simp only [pow_two, zero_mul, zero_add] at hfin
  nlinarith [hfin, hCS]

/--
**The one-dimensional Lieb–Thirring ground state bound (base case).**

Let `V ≤ 0` be an integrable potential on `ℝ` and let `ψ` be a normalized `C¹`
state with `ψ, ψ' ∈ L²(ℝ)` decaying at `-∞`.  Then the energy expectation value
satisfies

  `∫ (ψ')² + ∫ V ψ² ≥ - (∫ |V|)²`.

In particular the lowest eigenvalue `E₀` of `-d²/dx² + V` obeys `|E₀| ≤ (∫ |V|)²`,
the `d = 1`, `γ = 1/2` Lieb–Thirring inequality (with constant `1` rather than the
sharp constant `1/4`).
-/
theorem lieb_thirring_ground_state_1d (ψ : ℝ → ℝ) (hψ : ContDiff ℝ 1 ψ)
    (hL2 : MemLp ψ 2 volume) (hL2' : MemLp (deriv ψ) 2 volume)
    (hdecay : Tendsto ψ atBot (nhds 0)) (hnorm : ∫ y, ψ y ^ 2 = 1)
    (V : ℝ → ℝ) (hVle : ∀ y, V y ≤ 0) (hVint : Integrable V volume) :
    -(∫ y, |V y|) ^ 2 ≤ (∫ y, deriv ψ y ^ 2) + ∫ y, V y * ψ y ^ 2 := by
  set T := ∫ y, deriv ψ y ^ 2 with hTdef
  set A := ∫ y, |V y| with hAdef
  have hT0 : 0 ≤ T := integral_nonneg fun y => sq_nonneg _
  have hAV : A = -∫ y, V y := by
    rw [hAdef, ← integral_neg]
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => abs_of_nonpos (hVle y))
  -- The Sobolev sup bound, using the normalization `∫ ψ² = 1`.
  have hM : ∀ y, ψ y ^ 2 ≤ 2 * Real.sqrt T := by
    intro y
    have h := sobolev_sup_bound_1d ψ hψ hL2 hL2' hdecay y
    rwa [hnorm, Real.sqrt_one, mul_one] at h
  -- The potential energy is bounded below using `V ≤ 0`.
  have hVψ : Integrable (fun y => V y * ψ y ^ 2) volume := by
    have h := hVint.bdd_mul (f := fun y => ψ y ^ 2) (c := 2 * Real.sqrt T)
      ((hψ.continuous.pow 2).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hM y)
    simpa [mul_comm] using h
  have hpot : (2 * Real.sqrt T) * (∫ y, V y) ≤ ∫ y, V y * ψ y ^ 2 := by
    have hmono : ∫ y, (2 * Real.sqrt T) * V y ≤ ∫ y, V y * ψ y ^ 2 := by
      refine integral_mono (hVint.const_mul _) hVψ fun y => ?_
      have := mul_le_mul_of_nonpos_left (hM y) (hVle y)
      linarith [this]
    rwa [integral_const_mul] at hmono
  -- Complete the square.
  have hs : Real.sqrt T ^ 2 = T := Real.sq_sqrt hT0
  have hsq : 0 ≤ (Real.sqrt T - A) ^ 2 := sq_nonneg _
  have hVsum : (2 * Real.sqrt T) * (∫ y, V y) = -(2 * A * Real.sqrt T) := by
    rw [show (∫ y, V y) = -A by rw [hAV]; ring]
    ring
  rw [hVsum] at hpot
  nlinarith [hpot, hs, hsq]

end OneDimensional

end Frontier

