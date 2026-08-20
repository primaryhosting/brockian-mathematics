/-
# Mirzakhani WP Volume
Category: Frontier — Fields Medal Work
Target: Frontier.mirzakhani_WP_volume
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Mirzakhani WP Volume
Category: Frontier — Fields Medal Work
Target: Frontier.mirzakhani_WP_volume
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

set_option grind.warning false

/-!
## Overview

Mathlib contains no theory of moduli spaces of bordered Riemann surfaces or of
Weil–Petersson volumes, so the objects entering Mirzakhani's recursion are defined here from
scratch.  The two nontrivial inputs taken from Mathlib are the Basel sum `hasSum_zeta_two`
(`∑ 1 / n ^ 2 = π ^ 2 / 6`) and the Gamma-integral evaluation
`Real.integral_rpow_mul_exp_neg_mul_Ioi`; everything else (the Fermi–Dirac integral
`∫₀^∞ v / (1 + e ^ v) dv = π ^ 2 / 12`, the first moment of Mirzakhani's kernel, and the
recursion itself) is proved below.
-/

namespace Frontier

open MeasureTheory Set

/-! ## The Fermi–Dirac weight and Mirzakhani's kernel -/

/-- The Fermi–Dirac weight `σ (y) = 1 / (1 + e ^ y)` occurring in Mirzakhani's kernel. -/
noncomputable def fermi (y : ℝ) : ℝ := 1 / (1 + Real.exp y)

/-- Mirzakhani's integration kernel
`H (x, t) = 1 / (1 + e ^ ((x + t) / 2)) + 1 / (1 + e ^ ((x - t) / 2))`. -/
noncomputable def mirzakhaniH (x t : ℝ) : ℝ := fermi ((x + t) / 2) + fermi ((x - t) / 2)

/-- The first moment `F₁ (t) = ∫₀^∞ x · H (x, t) dx` of Mirzakhani's kernel. -/
noncomputable def F₁ (t : ℝ) : ℝ := ∫ x in Ioi (0 : ℝ), x * mirzakhaniH x t

/-! ## Weil–Petersson volumes in the two smallest cases -/

/-- The Weil–Petersson volume of the moduli space of bordered pairs of pants:
`V_{0,3} (L₁, L₂, L₃) = 1`. -/
def V₀₃ (_L₁ _L₂ _L₃ : ℝ) : ℝ := 1

/-- The Weil–Petersson volume of the moduli space of bordered genus-`0` surfaces with four
boundary components: `V_{0,4} (L) = 2 π² + (L₁² + L₂² + L₃² + L₄²) / 2`. -/
noncomputable def V₀₄ (L₁ L₂ L₃ L₄ : ℝ) : ℝ :=
  2 * Real.pi ^ 2 + (L₁ ^ 2 + L₂ ^ 2 + L₃ ^ 2 + L₄ ^ 2) / 2

/-- The right-hand side of Mirzakhani's recursion for `(g, n) = (0, 4)`.

In general the right-hand side is a sum of three groups of terms: the two "pair of pants"
terms `A^{con}` (gluing the two new boundary components to one connected surface of genus
`g - 1`) and `A^{dcon}` (splitting off two stable pieces), and the terms `B` coming from
gluing the first boundary to the `j`-th one.  For `(g, n) = (0, 4)` both `A`-terms are empty:
`A^{con}` needs `g ≥ 1`, and every splitting of `{L₂, L₃, L₄}` into two pieces leaves an
unstable component.  Hence only the `B`-terms, recorded below, survive; each of them involves
the volume `V_{0,3}` of a pair of pants. -/
noncomputable def mirzakhaniRHS₀₄ (L₁ L₂ L₃ L₄ : ℝ) : ℝ :=
  (1 / 2) *
    ((∫ x in Ioi (0 : ℝ),
        x * (mirzakhaniH x (L₁ + L₂) + mirzakhaniH x (L₁ - L₂)) * V₀₃ x L₃ L₄) +
     (∫ x in Ioi (0 : ℝ),
        x * (mirzakhaniH x (L₁ + L₃) + mirzakhaniH x (L₁ - L₃)) * V₀₃ x L₂ L₄) +
     (∫ x in Ioi (0 : ℝ),
        x * (mirzakhaniH x (L₁ + L₄) + mirzakhaniH x (L₁ - L₄)) * V₀₃ x L₂ L₃))

/-! ## Basic properties of `fermi` -/

lemma fermi_pos (y : ℝ) : 0 < fermi y := by
  have : (0:ℝ) < 1 + Real.exp y := by positivity
  simpa [fermi] using div_pos one_pos this

lemma fermi_add_fermi_neg (y : ℝ) : fermi y + fermi (-y) = 1 := by
  have h1 : (0:ℝ) < 1 + Real.exp y := by positivity
  have h2 : (0:ℝ) < 1 + Real.exp (-y) := by positivity
  have hpos : (0:ℝ) < Real.exp y := Real.exp_pos y
  have hy : Real.exp (-y) = (Real.exp y)⁻¹ := Real.exp_neg y
  rw [fermi, fermi, hy]
  rw [div_add_div _ _ (by positivity) (by positivity), div_eq_one_iff_eq (by positivity)]
  field_simp
  ring

lemma continuous_fermi : Continuous fermi := by
  refine Continuous.div continuous_const (by fun_prop) ?_
  intro y
  positivity

lemma fermi_le_exp_neg (y : ℝ) : fermi y ≤ Real.exp (-y) := by
  have hpos : (0:ℝ) < 1 + Real.exp y := by positivity
  rw [fermi, Real.exp_neg, div_le_iff₀ hpos, inv_mul_eq_div, le_div_iff₀ (Real.exp_pos y)]
  linarith

/-- The elementary bound `v ≤ e ^ (v / 2)` for `v ≥ 0`. -/
lemma le_exp_half {v : ℝ} (hv : 0 ≤ v) : v ≤ Real.exp (v / 2) := by
  have h : 1 + v / 4 ≤ Real.exp (v / 4) := by
    have := Real.add_one_le_exp (v / 4)
    linarith
  have hpos : (0:ℝ) ≤ 1 + v / 4 := by linarith
  have hsq : (1 + v / 4) ^ 2 ≤ (Real.exp (v / 4)) ^ 2 := by
    exact pow_le_pow_left₀ hpos h 2
  have hexp : (Real.exp (v / 4)) ^ 2 = Real.exp (v / 2) := by
    rw [← Real.exp_nat_mul]
    norm_num
    ring_nf
  nlinarith [sq_nonneg (v - 4)]

/-! ## Integrability -/

lemma integrableOn_fermi (c : ℝ) : IntegrableOn fermi (Ioi c) := by
  refine integrable_of_isBigO_exp_neg (b := 1) one_pos
    (continuous_fermi.continuousOn) ?_
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [Filter.eventually_ge_atTop (0:ℝ)] with v hv
  have h := fermi_le_exp_neg v
  have hp := (fermi_pos v).le
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (fermi_pos v),
    abs_of_pos (Real.exp_pos _)]
  simpa using h.trans_eq (by ring_nf)

lemma integrableOn_id_mul_fermi (c : ℝ) :
    IntegrableOn (fun v => v * fermi v) (Ioi c) := by
  refine integrable_of_isBigO_exp_neg (b := 1/2) (by norm_num)
    ((continuous_id.mul continuous_fermi).continuousOn) ?_
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [Filter.eventually_ge_atTop (0:ℝ)] with v hv
  have h := fermi_le_exp_neg v
  have hv2 : v ≤ Real.exp (v / 2) := le_exp_half hv
  have key : v * fermi v ≤ Real.exp (-(1/2) * v) := by
    calc v * fermi v ≤ Real.exp (v/2) * Real.exp (-v) := by
          apply mul_le_mul hv2 h (fermi_pos v).le (Real.exp_pos _).le
      _ = Real.exp (-(1/2) * v) := by
          rw [← Real.exp_add]; ring_nf
  have hnn : 0 ≤ v * fermi v := mul_nonneg hv (fermi_pos v).le
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnn,
    abs_of_pos (Real.exp_pos _)]
  linarith

lemma integrableOn_id_mul_fermi_affine {c : ℝ} (hc : 0 < c) (d r : ℝ) :
    IntegrableOn (fun x => x * fermi (c * x + d)) (Ioi r) := by
  refine integrable_of_isBigO_exp_neg (b := c/2) (by positivity)
    ((continuous_id.mul (continuous_fermi.comp (by fun_prop))).continuousOn) ?_
  refine Asymptotics.IsBigO.of_bound (Real.exp (-d) / c) ?_
  filter_upwards [Filter.eventually_ge_atTop (0:ℝ),
    Filter.eventually_ge_atTop (-d/c)] with x hx hxd
  have hnn : 0 ≤ x * fermi (c * x + d) := mul_nonneg hx (fermi_pos _).le
  have h1 : fermi (c * x + d) ≤ Real.exp (-(c * x + d)) := fermi_le_exp_neg _
  have h2 : c * x ≤ Real.exp (c * x / 2) := le_exp_half (by positivity)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnn, abs_of_pos (Real.exp_pos _)]
  have hx' : x ≤ Real.exp (c * x / 2) / c := by
    rw [le_div_iff₀ hc]; linarith [h2]
  calc x * fermi (c * x + d)
      ≤ (Real.exp (c * x / 2) / c) * Real.exp (-(c * x + d)) := by
        apply mul_le_mul hx' h1 (fermi_pos _).le (by positivity)
    _ = (Real.exp (-d) / c) * Real.exp (-(c/2) * x) := by
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← Real.exp_add, ← Real.exp_add]
        ring_nf

/-! ## The basic Fermi–Dirac integral `∫₀^∞ v / (1 + e^v) dv = π² / 12` -/

/-- `∑ 1 / (n + 1) ^ 2 = π ^ 2 / 6`, the Basel problem in shifted indexing. -/
lemma hasSum_shift : HasSum (fun n : ℕ => 1 / ((n:ℝ) + 1) ^ 2) (Real.pi ^ 2 / 6) := by
  have hinj : Function.Injective (fun n : ℕ => n + 1) := fun a b h => by
    simp only [add_left_inj] at h; exact h
  have hzero : ∀ x : ℕ, x ∉ Set.range (fun n : ℕ => n + 1) → 1 / ((x:ℝ))^2 = 0 := by
    intro x hx
    have hx0 : x = 0 := by
      by_contra h
      exact hx ⟨x - 1, by simp only []; omega⟩
    simp [hx0]
  have h := (hinj.hasSum_iff hzero).2 hasSum_zeta_two
  have heq : ((fun n : ℕ => 1 / ((n:ℝ))^2) ∘ (fun n : ℕ => n + 1))
      = fun n : ℕ => 1 / ((n:ℝ) + 1) ^ 2 := by
    funext n; simp [Function.comp]
  rwa [heq] at h

/-- `∑ 1 / (2 n + 1) ^ 2 = π ^ 2 / 8`. -/
lemma hasSum_odd_zeta_two :
    HasSum (fun k : ℕ => 1 / ((2 * k + 1 : ℕ) : ℝ) ^ 2) (Real.pi ^ 2 / 8) := by
  have hinj : Function.Injective (fun k : ℕ => 2 * k + 1) := fun a b h => by
    simp only [] at h; omega
  have hcomp : (fun k : ℕ => 1 / ((2 * k + 1 : ℕ) : ℝ) ^ 2)
      = (fun n : ℕ => 1 / ((n:ℝ))^2) ∘ (fun k : ℕ => 2 * k + 1) := rfl
  have hsummable : Summable (fun k : ℕ => 1 / ((2 * k + 1 : ℕ) : ℝ) ^ 2) := by
    rw [hcomp]; exact hasSum_zeta_two.summable.comp_injective hinj
  have heven : HasSum (fun k : ℕ => 1 / ((2 * k : ℕ) : ℝ) ^ 2) (Real.pi ^ 2 / 24) := by
    have h := hasSum_zeta_two.mul_left (1/4 : ℝ)
    have heq : (fun k : ℕ => (1/4 : ℝ) * (1 / (k:ℝ)^2))
        = fun k : ℕ => 1 / ((2*k : ℕ):ℝ)^2 := by
      funext k
      push_cast
      rw [mul_pow]
      norm_num
      ring
    rw [heq] at h
    convert h using 1
    ring
  have hodd := hsummable.hasSum
  have h := HasSum.even_add_odd (f := fun n : ℕ => 1 / ((n:ℝ))^2) heven hodd
  have h2 := hasSum_zeta_two.unique h
  have heq2 : ∑' k : ℕ, 1 / ((2 * k + 1 : ℕ) : ℝ) ^ 2 = Real.pi ^ 2 / 8 := by linarith
  rwa [heq2] at hodd

/-- The alternating Basel sum `∑ (-1) ^ n / (n + 1) ^ 2 = π ^ 2 / 12`. -/
lemma hasSum_alt_zeta_two :
    HasSum (fun n : ℕ => (-1 : ℝ) ^ n / ((n : ℝ) + 1) ^ 2) (Real.pi ^ 2 / 12) := by
  have heven : HasSum (fun k : ℕ => (-1 : ℝ) ^ (2 * k) / (((2 * k : ℕ) : ℝ) + 1) ^ 2)
      (Real.pi ^ 2 / 8) := by
    have h := hasSum_odd_zeta_two
    have heq : (fun k : ℕ => 1 / ((2 * k + 1 : ℕ) : ℝ) ^ 2)
        = fun k : ℕ => (-1 : ℝ) ^ (2 * k) / (((2 * k : ℕ) : ℝ) + 1) ^ 2 := by
      funext k
      rw [pow_mul]
      push_cast
      norm_num
    rwa [heq] at h
  have hodd : HasSum (fun k : ℕ => (-1 : ℝ) ^ (2 * k + 1) / (((2 * k + 1 : ℕ) : ℝ) + 1) ^ 2)
      (-(Real.pi ^ 2 / 24)) := by
    have h := hasSum_shift.mul_left (-(1/4) : ℝ)
    have heq : (fun k : ℕ => (-(1/4) : ℝ) * (1 / ((k:ℝ) + 1) ^ 2))
        = fun k : ℕ => (-1 : ℝ) ^ (2 * k + 1) / (((2 * k + 1 : ℕ) : ℝ) + 1) ^ 2 := by
      funext k
      have h1 : (-1:ℝ) ^ (2 * k + 1) = -1 := by
        rw [pow_succ, pow_mul]; norm_num
      rw [h1]
      push_cast
      rw [show ((2:ℝ) * (k:ℝ) + 1 + 1) = 2 * ((k:ℝ) + 1) by ring, mul_pow]
      have hk : ((k:ℝ) + 1) ^ 2 ≠ 0 := by positivity
      field_simp
      norm_num
    rw [heq] at h
    convert h using 1
    ring
  have h := HasSum.even_add_odd (f := fun n : ℕ => (-1 : ℝ) ^ n / ((n : ℝ) + 1) ^ 2) heven hodd
  convert h using 1
  ring

lemma hasSum_fermi_series {v : ℝ} (hv : 0 < v) :
    HasSum (fun n : ℕ => (-1 : ℝ) ^ n * (v * Real.exp (-(((n : ℝ) + 1) * v))))
      (v * fermi v) := by
  have hlt : ‖(-Real.exp (-v))‖ < 1 := by
    rw [norm_neg, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc Real.exp (-v) < Real.exp 0 := Real.exp_lt_exp.2 (by linarith)
      _ = 1 := Real.exp_zero
  have h := (hasSum_geometric_of_norm_lt_one hlt).mul_left (v * Real.exp (-v))
  have heq : (fun n : ℕ => v * Real.exp (-v) * (-Real.exp (-v)) ^ n)
      = fun n : ℕ => (-1 : ℝ) ^ n * (v * Real.exp (-(((n : ℝ) + 1) * v))) := by
    funext n
    rw [neg_pow, ← Real.exp_nat_mul]
    rw [show -(((n:ℝ) + 1) * v) = (n : ℝ) * -v + -v by ring, Real.exp_add]
    ring
  rw [heq] at h
  have hval : v * Real.exp (-v) * (1 - -Real.exp (-v))⁻¹ = v * fermi v := by
    have hpos : (0:ℝ) < Real.exp v := Real.exp_pos v
    rw [fermi, Real.exp_neg]
    field_simp
    rw [sub_neg_eq_add, add_comm (Real.exp v) 1, div_self (by positivity)]
  rwa [hval] at h

lemma integral_id_mul_exp (n : ℕ) :
    ∫ v in Ioi (0:ℝ), v * Real.exp (-(((n : ℝ) + 1) * v)) = 1 / ((n : ℝ) + 1) ^ 2 := by
  have hr : (0:ℝ) < (n : ℝ) + 1 := by positivity
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := (n:ℝ) + 1) (by norm_num) hr
  rw [Real.Gamma_two] at h
  calc ∫ v in Ioi (0:ℝ), v * Real.exp (-(((n : ℝ) + 1) * v))
      = ∫ t in Ioi (0:ℝ), t ^ ((2:ℝ) - 1) * Real.exp (-(((n:ℝ) + 1) * t)) := by
        refine setIntegral_congr_fun measurableSet_Ioi (fun v _ => ?_)
        norm_num
    _ = (1/((n:ℝ)+1))^(2:ℝ) * 1 := h
    _ = 1 / ((n : ℝ) + 1) ^ 2 := by
        rw [mul_one, show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast, div_pow, one_pow]

lemma integrableOn_id_mul_exp (n : ℕ) :
    IntegrableOn (fun v => v * Real.exp (-(((n : ℝ) + 1) * v))) (Ioi (0:ℝ)) := by
  refine integrable_of_isBigO_exp_neg (b := 1/2) (by norm_num)
    ((continuous_id.mul (Real.continuous_exp.comp (by fun_prop))).continuousOn) ?_
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [Filter.eventually_ge_atTop (0:ℝ)] with v hv
  have hle : Real.exp (-(((n : ℝ) + 1) * v)) ≤ Real.exp (-v) := by
    refine Real.exp_le_exp.2 ?_
    have h1 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    nlinarith
  have h2 : v ≤ Real.exp (v / 2) := le_exp_half hv
  have hnn : 0 ≤ v * Real.exp (-(((n : ℝ) + 1) * v)) := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnn, abs_of_pos (Real.exp_pos _)]
  have hb : v * Real.exp (-(((n : ℝ) + 1) * v)) ≤ Real.exp (v/2) * Real.exp (-v) :=
    mul_le_mul h2 hle (Real.exp_pos _).le (Real.exp_pos _).le
  have heq : Real.exp (v/2) * Real.exp (-v) = Real.exp (-(1/2) * v) := by
    rw [← Real.exp_add]; ring_nf
  rw [heq] at hb
  linarith

lemma integral_Ioi_zero_id_mul_fermi :
    ∫ v in Ioi (0:ℝ), v * fermi v = Real.pi ^ 2 / 12 := by
  set F : ℕ → ℝ → ℝ := fun n v => (-1 : ℝ) ^ n * (v * Real.exp (-(((n : ℝ) + 1) * v)))
    with hF
  have hint : ∀ n, IntegrableOn (F n) (Ioi (0:ℝ)) := fun n =>
    (integrableOn_id_mul_exp n).const_mul _
  have hmeas : ∀ n, AEStronglyMeasurable (F n) (volume.restrict (Ioi (0:ℝ))) :=
    fun n => (hint n).aestronglyMeasurable
  have hnormint : ∀ n, ∫ v in Ioi (0:ℝ), ‖F n v‖ = 1 / ((n:ℝ)+1)^2 := by
    intro n
    rw [← integral_id_mul_exp n]
    refine setIntegral_congr_fun measurableSet_Ioi (fun v hv => ?_)
    have hv' : (0:ℝ) < v := hv
    rw [hF]
    simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    rw [Real.norm_eq_abs, abs_of_nonneg hv'.le, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
  have hfin : ∑' n : ℕ, ∫⁻ v in Ioi (0:ℝ), ‖F n v‖ₑ ≠ ⊤ := by
    have hcast : ∀ n : ℕ, ∫⁻ v in Ioi (0:ℝ), ‖F n v‖ₑ = ENNReal.ofReal (1 / ((n:ℝ)+1)^2) := by
      intro n
      rw [← hnormint n, ofReal_integral_norm_eq_lintegral_enorm (hint n)]
    rw [tsum_congr hcast, ← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
      hasSum_shift.summable]
    exact ENNReal.ofReal_ne_top
  have hts := integral_tsum hmeas hfin
  have hlhs : ∫ v in Ioi (0:ℝ), ∑' n : ℕ, F n v = ∫ v in Ioi (0:ℝ), v * fermi v :=
    setIntegral_congr_fun measurableSet_Ioi (fun v hv => (hasSum_fermi_series hv).tsum_eq)
  have hrhs : ∑' n : ℕ, ∫ v in Ioi (0:ℝ), F n v = Real.pi ^ 2 / 12 := by
    have hterm : ∀ n : ℕ, ∫ v in Ioi (0:ℝ), F n v = (-1:ℝ)^n / ((n:ℝ)+1)^2 := by
      intro n
      rw [hF]
      simp only
      rw [integral_const_mul, integral_id_mul_exp n]
      ring
    rw [tsum_congr hterm]
    exact hasSum_alt_zeta_two.tsum_eq
  rw [← hlhs, hts, hrhs]

/-! ## Symmetric interval integrals -/

lemma intervalIntegral_symm_fermi (a : ℝ) :
    ∫ v in (-a)..a, fermi v = a := by
  have hint : ∀ p q : ℝ, IntervalIntegrable fermi volume p q :=
    fun p q => continuous_fermi.intervalIntegrable p q
  have hsplit : (∫ v in (-a)..(0:ℝ), fermi v) + ∫ v in (0:ℝ)..a, fermi v
      = ∫ v in (-a)..a, fermi v :=
    intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _)
  have hneg : ∫ v in (0:ℝ)..a, fermi (-v) = ∫ v in (-a)..(0:ℝ), fermi v := by
    rw [intervalIntegral.integral_comp_neg]
    norm_num
  have hone : ∫ v in (0:ℝ)..a, fermi (-v) = a - ∫ v in (0:ℝ)..a, fermi v := by
    have hpt : ∀ v : ℝ, fermi (-v) = 1 - fermi v := fun v => by
      have := fermi_add_fermi_neg v; linarith
    simp_rw [hpt]
    rw [intervalIntegral.integral_sub intervalIntegrable_const (hint _ _)]
    simp
  linarith

lemma intervalIntegral_symm_id_mul_fermi (a : ℝ) :
    ∫ v in (-a)..a, v * fermi v = 2 * (∫ v in (0:ℝ)..a, v * fermi v) - a ^ 2 / 2 := by
  have hc : Continuous (fun v : ℝ => v * fermi v) := continuous_id.mul continuous_fermi
  have hint : ∀ p q : ℝ, IntervalIntegrable (fun v : ℝ => v * fermi v) volume p q :=
    fun p q => hc.intervalIntegrable p q
  have hsplit : (∫ v in (-a)..(0:ℝ), v * fermi v) + ∫ v in (0:ℝ)..a, v * fermi v
      = ∫ v in (-a)..a, v * fermi v :=
    intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _)
  have hneg : ∫ v in (0:ℝ)..a, (-v) * fermi (-v) = ∫ v in (-a)..(0:ℝ), v * fermi v := by
    rw [intervalIntegral.integral_comp_neg (fun v => v * fermi v)]
    norm_num
  have hone : ∫ v in (0:ℝ)..a, (-v) * fermi (-v)
      = (∫ v in (0:ℝ)..a, v * fermi v) - a ^ 2 / 2 := by
    have hpt : ∀ v : ℝ, (-v) * fermi (-v) = v * fermi v - v := fun v => by
      have h1 := fermi_add_fermi_neg v
      have h2 : fermi (-v) = 1 - fermi v := by linarith
      rw [h2]; ring
    simp_rw [hpt]
    rw [intervalIntegral.integral_sub (hint _ _) intervalIntegral.intervalIntegrable_id,
      integral_id]
    norm_num
  linarith

/-! ## Tail integrals -/

lemma tail_id_add (a : ℝ) (ha : 0 ≤ a) :
    (∫ v in Ioi a, v * fermi v) + (∫ v in Ioi (-a), v * fermi v)
      = Real.pi ^ 2 / 6 - a ^ 2 / 2 := by
  have hle : -a ≤ a := by linarith
  have hd : ∀ p : ℝ, Disjoint (Ioc p a) (Ioi a) := fun p => Ioc_disjoint_Ioi le_rfl
  have h1 : ∫ v in Ioi (-a), v * fermi v
      = (∫ v in Ioc (-a) a, v * fermi v) + ∫ v in Ioi a, v * fermi v := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi hle,
      setIntegral_union (hd _) measurableSet_Ioi
        ((integrableOn_id_mul_fermi (-a)).mono_set Ioc_subset_Ioi_self)
        (integrableOn_id_mul_fermi a)]
  have h2 : ∫ v in Ioi (0:ℝ), v * fermi v
      = (∫ v in Ioc (0:ℝ) a, v * fermi v) + ∫ v in Ioi a, v * fermi v := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi ha,
      setIntegral_union (hd _) measurableSet_Ioi
        ((integrableOn_id_mul_fermi 0).mono_set Ioc_subset_Ioi_self)
        (integrableOn_id_mul_fermi a)]
  have h3 : ∫ v in Ioc (-a) a, v * fermi v = ∫ v in (-a)..a, v * fermi v :=
    (intervalIntegral.integral_of_le hle).symm
  have h4 : ∫ v in Ioc (0:ℝ) a, v * fermi v = ∫ v in (0:ℝ)..a, v * fermi v :=
    (intervalIntegral.integral_of_le ha).symm
  have h5 := intervalIntegral_symm_id_mul_fermi a
  have h6 := integral_Ioi_zero_id_mul_fermi
  rw [h3] at h1
  rw [h4] at h2
  linarith

lemma tail_fermi_sub (a : ℝ) (ha : 0 ≤ a) :
    (∫ v in Ioi (-a), fermi v) - (∫ v in Ioi a, fermi v) = a := by
  have hle : -a ≤ a := by linarith
  have h1 : ∫ v in Ioi (-a), fermi v
      = (∫ v in Ioc (-a) a, fermi v) + ∫ v in Ioi a, fermi v := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi hle,
      setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
        ((integrableOn_fermi (-a)).mono_set Ioc_subset_Ioi_self)
        (integrableOn_fermi a)]
  have h3 : ∫ v in Ioc (-a) a, fermi v = ∫ v in (-a)..a, fermi v :=
    (intervalIntegral.integral_of_le hle).symm
  rw [h3, intervalIntegral_symm_fermi a] at h1
  linarith

/-! ## Scaling and translation -/

lemma integrableOn_id_mul_fermi_half (d r : ℝ) :
    IntegrableOn (fun x => x * fermi (x / 2 + d)) (Ioi r) := by
  have h := integrableOn_id_mul_fermi_affine (c := 1/2) (by norm_num) d r
  have heq : (fun x : ℝ => x * fermi (1/2 * x + d)) = fun x : ℝ => x * fermi (x / 2 + d) := by
    funext x
    rw [show (1:ℝ)/2 * x = x / 2 by ring]
  rwa [heq] at h

/-- Rescaling `x = 2 v` and translating turns the shifted first moment of `fermi` into tail
integrals. -/
lemma integral_shift_fermi (d : ℝ) :
    ∫ x in Ioi (0:ℝ), x * fermi (x / 2 + d)
      = 4 * ((∫ v in Ioi d, v * fermi v) - d * ∫ v in Ioi d, fermi v) := by
  have hscale : ∫ x in Ioi (0:ℝ), x * fermi (x / 2 + d)
      = 4 * ∫ u in Ioi (0:ℝ), u * fermi (u + d) := by
    have h := integral_comp_mul_left_Ioi (fun y : ℝ => 2 * y * fermi (y + d)) 0
      (b := 1/2) (by norm_num)
    simp only [smul_eq_mul] at h
    rw [show ((1:ℝ)/2 * 0) = 0 by ring] at h
    have hl : ∫ x in Ioi (0:ℝ), 2 * ((1:ℝ)/2 * x) * fermi ((1:ℝ)/2 * x + d)
        = ∫ x in Ioi (0:ℝ), x * fermi (x / 2 + d) := by
      refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
      rw [show (2:ℝ) * ((1:ℝ)/2 * x) = x by ring, show (1:ℝ)/2 * x = x / 2 by ring]
    rw [hl] at h
    rw [h]
    have hc : ∫ y in Ioi (0:ℝ), 2 * y * fermi (y + d)
        = 2 * ∫ y in Ioi (0:ℝ), y * fermi (y + d) := by
      rw [← integral_const_mul]
      exact setIntegral_congr_fun measurableSet_Ioi (fun x _ => by ring)
    rw [hc]
    ring
  have htrans : ∫ u in Ioi (0:ℝ), u * fermi (u + d)
      = ∫ v in Ioi d, (v - d) * fermi v := by
    have h := (measurePreserving_add_right (volume : Measure ℝ) d).setIntegral_preimage_emb
      (measurableEmbedding_addRight d) (fun v => (v - d) * fermi v) (Ioi d)
    have hpre : (fun x : ℝ => x + d) ⁻¹' (Ioi d) = Ioi (0:ℝ) := by
      ext x; simp [Set.mem_Ioi]
    rw [hpre] at h
    rw [← h]
    exact setIntegral_congr_fun measurableSet_Ioi (fun x _ => by ring_nf)
  have hsplit : ∫ v in Ioi d, (v - d) * fermi v
      = (∫ v in Ioi d, v * fermi v) - d * ∫ v in Ioi d, fermi v := by
    have hi1 := integrableOn_id_mul_fermi d
    have hi2 := (integrableOn_fermi d).const_mul d
    rw [← integral_const_mul, ← integral_sub hi1 hi2]
    exact setIntegral_congr_fun measurableSet_Ioi (fun x _ => by ring)
  rw [hscale, htrans, hsplit]

/-! ## Evaluation of the first moment of Mirzakhani's kernel -/

lemma F₁_eq_of_nonneg {t : ℝ} (ht : 0 ≤ t) : F₁ t = t ^ 2 / 2 + 2 * Real.pi ^ 2 / 3 := by
  have ha : (0:ℝ) ≤ t / 2 := by linarith
  have hsplit : F₁ t = (∫ x in Ioi (0:ℝ), x * fermi (x / 2 + t / 2))
      + ∫ x in Ioi (0:ℝ), x * fermi (x / 2 + (-(t / 2))) := by
    rw [F₁, ← integral_add (integrableOn_id_mul_fermi_half (t/2) 0)
      (integrableOn_id_mul_fermi_half (-(t/2)) 0)]
    refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
    rw [mirzakhaniH, show (x + t)/2 = x/2 + t/2 by ring,
      show (x - t)/2 = x/2 + (-(t/2)) by ring]
    ring
  rw [hsplit, integral_shift_fermi (t/2), integral_shift_fermi (-(t/2))]
  have h1 := tail_id_add (t/2) ha
  have h2 := tail_fermi_sub (t/2) ha
  linear_combination 4 * h1 + 2 * t * h2

lemma mirzakhaniH_neg (x t : ℝ) : mirzakhaniH x (-t) = mirzakhaniH x t := by
  have h1 : x + -t = x - t := by ring
  have h2 : x - -t = x + t := by ring
  rw [mirzakhaniH, mirzakhaniH, h1, h2, add_comm]

/-- Mirzakhani's first-moment integral: `∫₀^∞ x H (x, t) dx = t² / 2 + 2π² / 3`. -/
theorem F₁_eq (t : ℝ) : F₁ t = t ^ 2 / 2 + 2 * Real.pi ^ 2 / 3 := by
  rcases le_total 0 t with h | h
  · exact F₁_eq_of_nonneg h
  · have h' : (0:ℝ) ≤ -t := by linarith
    have : F₁ (-t) = (-t) ^ 2 / 2 + 2 * Real.pi ^ 2 / 3 := F₁_eq_of_nonneg h'
    have hE : F₁ (-t) = F₁ t := by
      simp only [F₁]
      simp only [mirzakhaniH_neg]
    rw [← hE, this]
    ring

/-! ## Mirzakhani's recursion in the case `(g, n) = (0, 4)` -/

lemma integrableOn_id_mul_mirzakhaniH (t : ℝ) :
    IntegrableOn (fun x => x * mirzakhaniH x t) (Ioi (0:ℝ)) := by
  have h : IntegrableOn
      (fun x : ℝ => x * fermi (x / 2 + t / 2) + x * fermi (x / 2 + (-(t / 2)))) (Ioi (0:ℝ)) :=
    (integrableOn_id_mul_fermi_half (t/2) 0).add (integrableOn_id_mul_fermi_half (-(t/2)) 0)
  refine MeasureTheory.IntegrableOn.congr_fun h (fun x _ => ?_) measurableSet_Ioi
  rw [mirzakhaniH, show (x + t)/2 = x/2 + t/2 by ring,
    show (x - t)/2 = x/2 + (-(t/2)) by ring]
  ring

lemma integral_pair (u w c₁ c₂ : ℝ) :
    (∫ x in Ioi (0:ℝ), x * (mirzakhaniH x u + mirzakhaniH x w) * V₀₃ x c₁ c₂)
      = F₁ u + F₁ w := by
  rw [F₁, F₁, ← integral_add (integrableOn_id_mul_mirzakhaniH u)
    (integrableOn_id_mul_mirzakhaniH w)]
  refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
  rw [V₀₃]
  ring

lemma mirzakhaniRHS₀₄_eq (L₁ L₂ L₃ L₄ : ℝ) :
    mirzakhaniRHS₀₄ L₁ L₂ L₃ L₄
      = 2 * Real.pi ^ 2 + (3 * L₁ ^ 2 + L₂ ^ 2 + L₃ ^ 2 + L₄ ^ 2) / 2 := by
  rw [mirzakhaniRHS₀₄, integral_pair, integral_pair, integral_pair,
    F₁_eq, F₁_eq, F₁_eq, F₁_eq, F₁_eq, F₁_eq]
  ring

lemma deriv_L_mul_V₀₄ (L₁ L₂ L₃ L₄ : ℝ) :
    deriv (fun s => s * V₀₄ s L₂ L₃ L₄) L₁
      = 2 * Real.pi ^ 2 + (3 * L₁ ^ 2 + L₂ ^ 2 + L₃ ^ 2 + L₄ ^ 2) / 2 := by
  have hf : (fun s => s * V₀₄ s L₂ L₃ L₄)
      = fun s : ℝ => 2 * Real.pi ^ 2 * s + s ^ 3 / 2 + ((L₂ ^ 2 + L₃ ^ 2 + L₄ ^ 2) / 2) * s := by
    funext s; simp only [V₀₄]; ring
  have h1 : HasDerivAt (fun s : ℝ => s ^ 3) (3 * L₁ ^ 2) L₁ := by
    simpa using hasDerivAt_pow 3 L₁
  have h : HasDerivAt
      (fun s : ℝ => 2 * Real.pi ^ 2 * s + s ^ 3 / 2 + ((L₂ ^ 2 + L₃ ^ 2 + L₄ ^ 2) / 2) * s)
      (2 * Real.pi ^ 2 + 3 * L₁ ^ 2 / 2 + (L₂ ^ 2 + L₃ ^ 2 + L₄ ^ 2) / 2) L₁ := by
    have := (((hasDerivAt_id L₁).const_mul (2 * Real.pi ^ 2)).add (h1.div_const 2)).add
      ((hasDerivAt_id L₁).const_mul ((L₂ ^ 2 + L₃ ^ 2 + L₄ ^ 2) / 2))
    simpa using this
  rw [hf, h.deriv]; ring

/-- Mirzakhani's recursion, together with the base case `V_{0,3} = 1`, *determines* the volume
`V_{0,4}`: any function `W` for which `s ↦ s · W (s)` is differentiable and satisfies the
recursion agrees with `V_{0,4}`. -/
theorem V₀₄_of_recursion (L₂ L₃ L₄ : ℝ) (W : ℝ → ℝ)
    (hW : Differentiable ℝ (fun s => s * W s))
    (hrec : ∀ s : ℝ, deriv (fun r => r * W r) s = mirzakhaniRHS₀₄ s L₂ L₃ L₄) (s : ℝ) :
    s * W s = s * V₀₄ s L₂ L₃ L₄ := by
  have hdiffV : Differentiable ℝ (fun r : ℝ => r * V₀₄ r L₂ L₃ L₄) := by
    have hpoly : (fun r : ℝ => r * V₀₄ r L₂ L₃ L₄)
        = fun r : ℝ => 2 * Real.pi ^ 2 * r + r ^ 3 / 2 + ((L₂ ^ 2 + L₃ ^ 2 + L₄ ^ 2) / 2) * r := by
      funext r; simp only [V₀₄]; ring
    rw [hpoly]; fun_prop
  have hg : Differentiable ℝ (fun r : ℝ => r * W r - r * V₀₄ r L₂ L₃ L₄) := hW.sub hdiffV
  have hderiv : ∀ r : ℝ, deriv (fun r : ℝ => r * W r - r * V₀₄ r L₂ L₃ L₄) r = 0 := by
    intro r
    have h1 : HasDerivAt (fun q : ℝ => q * W q) (mirzakhaniRHS₀₄ r L₂ L₃ L₄) r := by
      have hd := (hW r).hasDerivAt
      rwa [hrec r] at hd
    have h2 : HasDerivAt (fun q : ℝ => q * V₀₄ q L₂ L₃ L₄) (mirzakhaniRHS₀₄ r L₂ L₃ L₄) r := by
      have hd := (hdiffV r).hasDerivAt
      rwa [deriv_L_mul_V₀₄ r L₂ L₃ L₄, ← mirzakhaniRHS₀₄_eq] at hd
    simpa using (h1.sub h2).deriv
  have hconst := is_const_of_deriv_eq_zero hg hderiv s 0
  simp only [zero_mul, sub_self] at hconst
  linarith

/-- **Mirzakhani's recursion for Weil–Petersson volumes**, base case and first step.

1. (Base case.)  The Weil–Petersson volume of the moduli space of bordered pairs of pants is
   `V_{0,3} ≡ 1`, independently of the boundary lengths.
2. (First moment of the kernel.)  Mirzakhani's kernel has first moment
   `∫₀^∞ x H (x, t) dx = t² / 2 + 2 π² / 3`.
3. (Recursion, and uniqueness of its solution.)  The volume polynomial
   `V_{0,4} (L) = 2 π² + (∑ Lᵢ²) / 2` satisfies Mirzakhani's recursion
   `∂/∂L₁ (L₁ · V_{0,4} (L)) = ½ ∑_{j = 2}^{4} ∫₀^∞ x (H (x, L₁ + L_j) + H (x, L₁ - L_j))
      V_{0,3} (x, …) dx`,
   whose right-hand side is built from the base case `V_{0,3}` alone (the two "pair of pants"
   terms of the general recursion are empty in this case for stability reasons). -/
theorem mirzakhani_WP_volume :
    (∀ L₁ L₂ L₃ : ℝ, V₀₃ L₁ L₂ L₃ = 1) ∧
    (∀ t : ℝ, ∫ x in Ioi (0:ℝ), x * mirzakhaniH x t = t ^ 2 / 2 + 2 * Real.pi ^ 2 / 3) ∧
    (∀ L₁ L₂ L₃ L₄ : ℝ,
      deriv (fun s => s * V₀₄ s L₂ L₃ L₄) L₁ = mirzakhaniRHS₀₄ L₁ L₂ L₃ L₄) ∧
    (∀ (L₂ L₃ L₄ : ℝ) (W : ℝ → ℝ), Differentiable ℝ (fun s => s * W s) →
      (∀ s : ℝ, deriv (fun r => r * W r) s = mirzakhaniRHS₀₄ s L₂ L₃ L₄) →
      ∀ s : ℝ, s * W s = s * V₀₄ s L₂ L₃ L₄) := by
  refine ⟨fun _ _ _ => rfl, fun t => F₁_eq t, fun L₁ L₂ L₃ L₄ => ?_,
    fun L₂ L₃ L₄ W hW hrec => V₀₄_of_recursion L₂ L₃ L₄ W hW hrec⟩
  rw [deriv_L_mul_V₀₄, mirzakhaniRHS₀₄_eq]

end Frontier

