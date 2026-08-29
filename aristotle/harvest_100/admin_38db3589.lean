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

open MeasureTheory Set Real Asymptotics

namespace Frontier

/-! ## Mirzakhani's integration kernel -/

/-- The basic "logistic" profile appearing in Mirzakhani's kernels:
`logistic u = 1 / (1 + exp (u / 2))`. -/
noncomputable def logistic (u : ℝ) : ℝ := 1 / (1 + Real.exp (u / 2))

/-- Mirzakhani's integration kernel
`H (x, y) = 1/(1 + e^{(x+y)/2}) + 1/(1 + e^{(x-y)/2})`. -/
noncomputable def mirzKernel (x y : ℝ) : ℝ :=
  1 / (1 + Real.exp ((x + y) / 2)) + 1 / (1 + Real.exp ((x - y) / 2))

lemma mirzKernel_eq (x y : ℝ) : mirzKernel x y = logistic (x + y) + logistic (x - y) := rfl

lemma mirzKernel_neg (x y : ℝ) : mirzKernel x (-y) = mirzKernel x y := by
  simp [mirzKernel, sub_eq_add_neg, add_comm]

/-! ## The Weil–Petersson volume polynomials in the base cases -/

/-- The Weil–Petersson volume of the moduli space of hyperbolic pairs of pants
with boundary lengths `L₁, L₂, L₃` (a single point, so the volume is `1`). -/
def V03 (_L₁ _L₂ _L₃ : ℝ) : ℝ := 1

/-- The Weil–Petersson volume polynomial of `M_{0,4}`. -/
noncomputable def V04 (L₁ L₂ L₃ L₄ : ℝ) : ℝ :=
  2 * π ^ 2 + (L₁ ^ 2 + L₂ ^ 2 + L₃ ^ 2 + L₄ ^ 2) / 2

/-- The Weil–Petersson volume polynomial of `M_{1,1}`.

We use the orbifold normalisation `V_{1,1}(L) = (L² + 4π²)/48` (so that `V_{1,1}(0) = π²/12`),
which is the one for which Mirzakhani's recursion is stated with its usual constants; the
generic one-holed torus has the elliptic involution as an automorphism, which accounts for
the factor `2` relative to the normalisation `(L² + 4π²)/24`. -/
noncomputable def V11 (L : ℝ) : ℝ := (L ^ 2 + 4 * π ^ 2) / 48

/-! ## Elementary properties of the logistic profile -/

lemma logistic_pos (u : ℝ) : 0 < logistic u := by
  have : (0:ℝ) < 1 + Real.exp (u / 2) := by positivity
  simpa [logistic] using (one_div_pos.2 this)

lemma logistic_add_neg (u : ℝ) : logistic u + logistic (-u) = 1 := by
  have h1 : (0:ℝ) < 1 + Real.exp (u/2) := by positivity
  have h2 : (0:ℝ) < 1 + Real.exp (-(u/2)) := by positivity
  have h3 : Real.exp (u/2) * Real.exp (-(u/2)) = 1 := by
    rw [← Real.exp_add]; ring_nf; simp
  simp only [logistic, neg_div]
  field_simp
  nlinarith [h3]

lemma logistic_le_exp (u : ℝ) : logistic u ≤ Real.exp (-u / 2) := by
  have h1 : (0:ℝ) < 1 + Real.exp (u/2) := by positivity
  have h3 : Real.exp (-u/2) * Real.exp (u/2) = 1 := by
    rw [← Real.exp_add]; ring_nf; simp
  rw [logistic, div_le_iff₀ h1]
  nlinarith [Real.exp_pos (-u/2)]

lemma continuous_logistic : Continuous logistic := by
  unfold logistic
  fun_prop (disch := intro x; positivity)

/-! ## Integrability -/

/-- Integrability of `x ↦ (b x + c) · logistic (x + d)` on any half-line. -/
lemma integrableOn_affine_mul_logistic (a b c d : ℝ) :
    IntegrableOn (fun x => (b * x + c) * logistic (x + d)) (Ioi a) volume := by
  apply integrable_of_isBigO_exp_neg (b := 1/4) (by norm_num)
  · exact (((continuous_const.mul continuous_id).add continuous_const).mul
      (continuous_logistic.comp (continuous_id.add continuous_const))).continuousOn
  · rw [isBigO_iff]
    refine ⟨Real.exp (-d/2) * (4 * |b| + |c|), ?_⟩
    filter_upwards [Filter.eventually_ge_atTop (0:ℝ)] with y hy
    have hp : (0:ℝ) < Real.exp (-y/4) := Real.exp_pos _
    have hd : (0:ℝ) < Real.exp (-d/2) := Real.exp_pos _
    have e4 : Real.exp (-y/4) * Real.exp (y/4) = 1 := by rw [← Real.exp_add]; ring_nf; simp
    have hy4 : y * Real.exp (-y/4) ≤ 4 := by
      have h := Real.add_one_le_exp (y/4); nlinarith
    have hle1 : Real.exp (-y/4) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have hsplit : Real.exp (-(y+d)/2) = Real.exp (-d/2) * (Real.exp (-y/4) * Real.exp (-y/4)) := by
      rw [← Real.exp_add, ← Real.exp_add]; ring_nf
    have hbound : ‖(b * y + c) * logistic (y + d)‖ ≤ (|b| * y + |c|) * Real.exp (-(y+d)/2) := by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (logistic_pos _)]
      have hab : |b * y + c| ≤ |b| * y + |c| := by
        calc |b * y + c| ≤ |b * y| + |c| := abs_add_le _ _
        _ = |b| * y + |c| := by rw [abs_mul, abs_of_nonneg hy]
      have hL := logistic_le_exp (y + d)
      have hLpos := logistic_pos (y + d)
      have h0 : (0:ℝ) ≤ |b| * y + |c| := by positivity
      nlinarith [Real.exp_pos (-(y+d)/2), abs_nonneg (b * y + c)]
    have hnorm : ‖Real.exp (-(1/4:ℝ) * y)‖ = Real.exp (-y/4) := by
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]; ring_nf
    rw [hnorm]
    calc ‖(b * y + c) * logistic (y + d)‖ ≤ (|b| * y + |c|) * Real.exp (-(y+d)/2) := hbound
      _ = Real.exp (-d/2) * ((|b| * (y * Real.exp (-y/4))) * Real.exp (-y/4)
            + |c| * (Real.exp (-y/4) * Real.exp (-y/4))) := by rw [hsplit]; ring
      _ ≤ Real.exp (-d/2) * ((|b| * 4) * Real.exp (-y/4) + |c| * Real.exp (-y/4)) := by
          have h1 : (|b| * (y * Real.exp (-y/4))) * Real.exp (-y/4)
              ≤ (|b| * 4) * Real.exp (-y/4) := by
            have hb : |b| * (y * Real.exp (-y/4)) ≤ |b| * 4 :=
              mul_le_mul_of_nonneg_left hy4 (abs_nonneg b)
            exact mul_le_mul_of_nonneg_right hb hp.le
          have h2 : |c| * (Real.exp (-y/4) * Real.exp (-y/4)) ≤ |c| * Real.exp (-y/4) := by
            have hee : Real.exp (-y/4) * Real.exp (-y/4) ≤ Real.exp (-y/4) := by nlinarith
            exact mul_le_mul_of_nonneg_left hee (abs_nonneg c)
          nlinarith
      _ = Real.exp (-d/2) * (4 * |b| + |c|) * Real.exp (-y/4) := by ring

/-- Integrability of `y ↦ (b y + c) · logistic y` on any half-line. -/
lemma integrableOn_affine_mul_logistic' (a b c : ℝ) :
    IntegrableOn (fun y => (b * y + c) * logistic y) (Ioi a) volume := by
  simpa using integrableOn_affine_mul_logistic a b c 0

lemma integrableOn_lin_exp {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun y => y * Real.exp (-(r*y))) (Ioi 0) volume := by
  apply integrable_of_isBigO_exp_neg (b := r/2) (by linarith)
  · fun_prop
  · rw [isBigO_iff]
    refine ⟨2/r, ?_⟩
    filter_upwards [Filter.eventually_ge_atTop (0:ℝ)] with y hy
    have hp : (0:ℝ) < Real.exp (-(r/2*y)) := Real.exp_pos _
    have e4 : Real.exp (-(r/2*y)) * Real.exp (r/2*y) = 1 := by
      rw [← Real.exp_add]; ring_nf; simp
    have hy4 : y * Real.exp (-(r/2*y)) ≤ 2/r := by
      have h := Real.add_one_le_exp (r/2*y)
      have h2 : y * r ≤ 2 * Real.exp (r/2*y) := by nlinarith
      rw [le_div_iff₀ hr]
      nlinarith [mul_le_mul_of_nonneg_right h2 hp.le]
    have hsplit : Real.exp (-(r*y)) = Real.exp (-(r/2*y)) * Real.exp (-(r/2*y)) := by
      rw [← Real.exp_add]; ring_nf
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ y * Real.exp (-(r*y)))]
    have hre : Real.exp (-(r/2) * y) = Real.exp (-(r/2*y)) := by ring_nf
    rw [hre]
    calc y * Real.exp (-(r*y)) = (y * Real.exp (-(r/2*y))) * Real.exp (-(r/2*y)) := by
          rw [hsplit]; ring
      _ ≤ (2/r) * Real.exp (-(r/2*y)) := mul_le_mul_of_nonneg_right hy4 hp.le

/-! ## Translation of half-line integrals -/

lemma shift_Ioi (f : ℝ → ℝ) (c : ℝ) :
    ∫ x in Ioi (0:ℝ), f (x + c) = ∫ y in Ioi c, f y := by
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
  have hind : ∀ x : ℝ, (Ioi (0:ℝ)).indicator (fun x => f (x + c)) x
      = (Ioi c).indicator f (x + c) := by
    intro x
    simp [Set.indicator_apply]
  simp_rw [hind]
  exact integral_add_right_eq_self (fun y => (Ioi c).indicator f y) c

/-! ## The Fermi-type integral `∫₀^∞ y / (1 + e^{y/2}) dy = π²/3` -/

lemma integral_lin_exp {r : ℝ} (hr : 0 < r) :
    ∫ t in Ioi (0:ℝ), t * Real.exp (-(r*t)) = 1/r^2 := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := r) (by norm_num) hr
  rw [Real.Gamma_two] at h
  norm_num [Real.rpow_one] at h
  rw [h]
  field_simp

lemma hasSum_inv_sq_succ : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) (π ^ 2 / 6) := by
  have h := (hasSum_nat_add_iff (f := fun n : ℕ => 1 / ((n : ℝ)) ^ 2) 1
      (g := π^2/6 - ∑ i ∈ Finset.range 1, 1 / ((i:ℝ)) ^ 2)).2 (by simpa using hasSum_zeta_two)
  simpa using h

lemma hasSum_alternating_inv_sq :
    HasSum (fun n : ℕ => (-1 : ℝ) ^ n / ((n : ℝ) + 1) ^ 2) (π ^ 2 / 12) := by
  have hz := hasSum_inv_sq_succ
  set u : ℕ → ℝ := fun n => if Even n then 0 else 1 / ((n : ℝ) + 1) ^ 2 with hu_def
  have hinj : Function.Injective (fun k : ℕ => 2 * k + 1) := by
    intro a b h; simp only at h; omega
  have hsupp : ∀ n ∉ Set.range (fun k : ℕ => 2 * k + 1), u n = 0 := by
    intro n hn
    rcases Nat.even_or_odd n with h | h
    · simp [hu_def, h]
    · exfalso
      apply hn
      obtain ⟨k, hk⟩ := h
      exact ⟨k, by simp only; omega⟩
  have hcomp : HasSum (fun k : ℕ => u (2 * k + 1)) (π ^ 2 / 24) := by
    have heq : (fun k : ℕ => u (2 * k + 1)) = fun k : ℕ => (1/4 : ℝ) * (1 / ((k : ℝ) + 1) ^ 2) := by
      funext k
      have h1 : ¬ Even (2 * k + 1) := by simp [parity_simps]
      simp only [hu_def, h1, if_false]
      push_cast
      have hk : ((k:ℝ) + 1) ≠ 0 := by positivity
      field_simp
      ring
    rw [heq]
    have h2 := hz.mul_left (1/4 : ℝ)
    convert h2 using 1
    ring
  have hu : HasSum u (π ^ 2 / 24) := (hinj.hasSum_iff hsupp).1 hcomp
  have hfun : (fun n : ℕ => (-1 : ℝ) ^ n / ((n : ℝ) + 1) ^ 2)
      = fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2 - 2 * u n := by
    funext n
    rcases Nat.even_or_odd n with h | h
    · simp [hu_def, h, h.neg_one_pow]
    · have h1 : ¬ Even n := Nat.not_even_iff_odd.2 h
      simp only [hu_def, h1, if_false, h.neg_one_pow]
      ring
  rw [hfun]
  convert hz.sub (hu.mul_left 2) using 1
  ring

lemma hasSum_logistic_series {y : ℝ} (hy : 0 < y) :
    HasSum (fun n : ℕ => (-1:ℝ)^n * (y * Real.exp (-(((n:ℝ)+1)/2 * y)))) (y * logistic y) := by
  set q := Real.exp (-y/2) with hq
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := by rw [hq]; exact Real.exp_lt_one_iff.2 (by linarith)
  have hgeom : HasSum (fun n : ℕ => (-q)^n) (1 - (-q))⁻¹ := by
    apply hasSum_geometric_of_norm_lt_one
    rw [norm_neg, Real.norm_of_nonneg hq0.le]; exact hq1
  have hsum := hgeom.mul_left (y * q)
  have hfun : (fun n : ℕ => (-1:ℝ)^n * (y * Real.exp (-(((n:ℝ)+1)/2 * y))))
      = fun n : ℕ => y * q * (-q)^n := by
    funext n
    have harg : (n:ℝ) * (-y/2) + (-y/2) = -(((n:ℝ)+1)/2 * y) := by ring
    calc (-1:ℝ)^n * (y * Real.exp (-(((n:ℝ)+1)/2 * y)))
        = (-1:ℝ)^n * (y * Real.exp ((n:ℝ) * (-y/2) + (-y/2))) := by rw [harg]
      _ = y * q * (-q)^n := by
          rw [Real.exp_add, Real.exp_nat_mul, neg_pow, ← hq]; ring
  have hval : y * q * (1 - (-q))⁻¹ = y * logistic y := by
    have he : Real.exp (y/2) = q⁻¹ := by
      rw [hq, ← Real.exp_neg]; congr 1; ring
    unfold logistic
    rw [he, sub_neg_eq_add]
    field_simp
    ring
  rw [hfun, ← hval]
  exact hsum

lemma integral_lin_mul_logistic : ∫ y in Ioi (0:ℝ), y * logistic y = π ^ 2 / 3 := by
  set F : ℕ → ℝ → ℝ := fun n y => (-1)^n * (y * Real.exp (-(((n:ℝ)+1)/2 * y))) with hF
  have hr : ∀ n : ℕ, (0:ℝ) < ((n:ℝ)+1)/2 := by intro n; positivity
  have hInt : ∀ n : ℕ, IntegrableOn (F n) (Ioi 0) volume := fun n =>
    (integrableOn_lin_exp (hr n)).const_mul _
  have hvalF : ∀ n : ℕ, ∫ y in Ioi (0:ℝ), F n y = (-1)^n * (4/((n:ℝ)+1)^2) := by
    intro n
    rw [hF]; simp only
    rw [MeasureTheory.integral_const_mul, integral_lin_exp (hr n)]
    congr 1; field_simp; norm_num
  have hnormF : ∀ n : ℕ, ∫ y in Ioi (0:ℝ), ‖F n y‖ = 4/((n:ℝ)+1)^2 := by
    intro n
    have hcong : ∀ y ∈ Ioi (0:ℝ), ‖F n y‖ = y * Real.exp (-(((n:ℝ)+1)/2 * y)) := by
      intro y hy
      simp only [hF, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
        Real.norm_eq_abs, abs_of_pos (mem_Ioi.1 hy), abs_of_pos (Real.exp_pos _)]
    rw [setIntegral_congr_fun measurableSet_Ioi hcong, integral_lin_exp (hr n)]
    field_simp; norm_num
  have hsummable : Summable (fun n : ℕ => ∫ y in Ioi (0:ℝ), ‖F n y‖) := by
    apply ((hasSum_inv_sq_succ.summable).mul_left (4:ℝ)).congr
    intro n; rw [hnormF n]; field_simp
  have key := MeasureTheory.integral_tsum_of_summable_integral_norm hInt hsummable
  have hptw : ∀ y ∈ Ioi (0:ℝ), ∑' n : ℕ, F n y = y * logistic y :=
    fun y hy => (hasSum_logistic_series (mem_Ioi.1 hy)).tsum_eq
  rw [← setIntegral_congr_fun measurableSet_Ioi hptw, ← key]
  have hcv : ∀ n : ℕ, ∫ y in Ioi (0:ℝ), F n y = 4 * ((-1)^n / ((n:ℝ)+1)^2) := by
    intro n; rw [hvalF n]; ring
  rw [tsum_congr hcv, (hasSum_alternating_inv_sq.mul_left 4).tsum_eq]
  ring

/-! ## Mirzakhani's kernel integral -/

/-- The reflection step: `∫_{-t}^{t} (y+t) logistic y dy = t²/2 + ∫_0^t 2y logistic y dy`. -/
lemma integral_Ioc_reflect {t : ℝ} (ht : 0 ≤ t) :
    ∫ y in Ioc (-t) t, (y + t) * logistic y
      = t ^ 2 / 2 + ∫ y in Ioc (0:ℝ) t, 2 * y * logistic y := by
  have hcont : Continuous (fun y : ℝ => (y + t) * logistic y) :=
    (continuous_id.add continuous_const).mul continuous_logistic
  have hcont2 : Continuous (fun y : ℝ => 2 * y * logistic y) :=
    (continuous_const.mul continuous_id).mul continuous_logistic
  have hcont3 : Continuous (fun x : ℝ => (t - x) * (1 - logistic x)) :=
    (continuous_const.sub continuous_id).mul (continuous_const.sub continuous_logistic)
  have hcont4 : Continuous (fun x : ℝ => t - x) := continuous_const.sub continuous_id
  rw [← intervalIntegral.integral_of_le (by linarith : (-t:ℝ) ≤ t),
      ← intervalIntegral.integral_of_le ht]
  rw [← intervalIntegral.integral_add_adjacent_intervals
      (a := -t) (b := 0) (c := t) (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
  have hcn := intervalIntegral.integral_comp_neg (a := (0:ℝ)) (b := t)
      (fun y => (y + t) * logistic y)
  simp only [neg_zero] at hcn
  have hneg : ∫ y in (-t)..0, (y + t) * logistic y
      = ∫ x in (0:ℝ)..t, (t - x) * (1 - logistic x) := by
    rw [← hcn]
    apply intervalIntegral.integral_congr
    intro x _
    have h2 : logistic (-x) = 1 - logistic x := by have := logistic_add_neg x; linarith
    simp only [h2]
    ring
  rw [hneg, ← intervalIntegral.integral_add (hcont3.intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _)]
  have hpoint : ∫ x in (0:ℝ)..t, ((t - x) * (1 - logistic x) + (x + t) * logistic x)
      = ∫ x in (0:ℝ)..t, ((t - x) + 2 * x * logistic x) := by
    apply intervalIntegral.integral_congr
    intro x _
    simp only
    ring
  rw [hpoint, intervalIntegral.integral_add (hcont4.intervalIntegrable _ _)
      (hcont2.intervalIntegrable _ _)]
  congr 1
  rw [intervalIntegral.integral_sub intervalIntegrable_const intervalIntegral.intervalIntegrable_id]
  simp [integral_id]
  ring

/-- The basic kernel integral for nonnegative `t`. -/
lemma integral_mirzKernel_of_nonneg {t : ℝ} (ht : 0 ≤ t) :
    ∫ x in Ioi (0:ℝ), x * mirzKernel x t = t ^ 2 / 2 + 2 * π ^ 2 / 3 := by
  have iA : IntegrableOn (fun x => x * logistic (x + t)) (Ioi 0) volume := by
    simpa using integrableOn_affine_mul_logistic 0 1 0 t
  have iB : IntegrableOn (fun x => x * logistic (x + -t)) (Ioi 0) volume := by
    simpa using integrableOn_affine_mul_logistic 0 1 0 (-t)
  have i1 : IntegrableOn (fun y => (y + t) * logistic y) (Ioi (-t)) volume := by
    simpa using integrableOn_affine_mul_logistic' (-t) 1 t
  have i1' : IntegrableOn (fun y => (y + t) * logistic y) (Ioc (-t) t) volume :=
    i1.mono_set (fun x hx => hx.1)
  have i2 : IntegrableOn (fun y => (y + t) * logistic y) (Ioi t) volume := by
    simpa using integrableOn_affine_mul_logistic' t 1 t
  have i3 : IntegrableOn (fun y => (y - t) * logistic y) (Ioi t) volume := by
    have := integrableOn_affine_mul_logistic' t 1 (-t)
    refine this.congr_fun (fun x _ => by ring) measurableSet_Ioi
  have i4 : IntegrableOn (fun y => 2 * y * logistic y) (Ioi (0:ℝ)) volume := by
    have := integrableOn_affine_mul_logistic' 0 2 0
    refine this.congr_fun (fun x _ => by ring) measurableSet_Ioi
  have i4' : IntegrableOn (fun y => 2 * y * logistic y) (Ioc (0:ℝ) t) volume :=
    i4.mono_set (fun x hx => hx.1)
  have i4'' : IntegrableOn (fun y => 2 * y * logistic y) (Ioi t) volume :=
    i4.mono_set (fun x hx => lt_of_le_of_lt ht hx)
  -- split the kernel
  have hsplit : ∫ x in Ioi (0:ℝ), x * mirzKernel x t
      = (∫ x in Ioi (0:ℝ), x * logistic (x + t)) + ∫ x in Ioi (0:ℝ), x * logistic (x + -t) := by
    rw [← integral_add iA iB]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x _
    dsimp only
    rw [mirzKernel_eq, ← sub_eq_add_neg]
    ring
  have hA : ∫ x in Ioi (0:ℝ), x * logistic (x + t) = ∫ y in Ioi t, (y - t) * logistic y := by
    rw [← shift_Ioi (fun y => (y - t) * logistic y) t]
    exact setIntegral_congr_fun measurableSet_Ioi (fun x _ => by simp)
  have hB : ∫ x in Ioi (0:ℝ), x * logistic (x + -t) = ∫ y in Ioi (-t), (y + t) * logistic y := by
    rw [← shift_Ioi (fun y => (y + t) * logistic y) (-t)]
    exact setIntegral_congr_fun measurableSet_Ioi (fun x _ => by simp)
  have hdisj : Disjoint (Ioc (-t) t) (Ioi t) := by simp [Set.disjoint_left]
  have hunion : Ioc (-t) t ∪ Ioi t = Ioi (-t) := Set.Ioc_union_Ioi_eq_Ioi (by linarith)
  have hB2 : ∫ y in Ioi (-t), (y + t) * logistic y
      = (∫ y in Ioc (-t) t, (y + t) * logistic y) + ∫ y in Ioi t, (y + t) * logistic y := by
    rw [← hunion]
    exact setIntegral_union hdisj measurableSet_Ioi i1' i2
  -- combine the two half-line pieces above `t`
  have hIoi : (∫ y in Ioi t, (y - t) * logistic y) + ∫ y in Ioi t, (y + t) * logistic y
      = ∫ y in Ioi t, 2 * y * logistic y := by
    rw [← integral_add i3 i2]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x _
    dsimp only
    ring
  -- reassemble the half-line integral of `2 y logistic y`
  have hfull : (∫ y in Ioc (0:ℝ) t, 2 * y * logistic y) + ∫ y in Ioi t, 2 * y * logistic y
      = ∫ y in Ioi (0:ℝ), 2 * y * logistic y := by
    rw [← setIntegral_union (by simp [Set.disjoint_left]) measurableSet_Ioi i4' i4'',
      Set.Ioc_union_Ioi_eq_Ioi ht]
  have hval : ∫ y in Ioi (0:ℝ), 2 * y * logistic y = 2 * (π ^ 2 / 3) := by
    rw [← integral_lin_mul_logistic, ← MeasureTheory.integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x _
    ring
  rw [hsplit, hA, hB, hB2, integral_Ioc_reflect ht]
  have : (∫ y in Ioi t, (y - t) * logistic y)
      + (t ^ 2 / 2 + (∫ y in Ioc (0:ℝ) t, 2 * y * logistic y)
        + ∫ y in Ioi t, (y + t) * logistic y)
      = t ^ 2 / 2 + ((∫ y in Ioc (0:ℝ) t, 2 * y * logistic y)
        + ((∫ y in Ioi t, (y - t) * logistic y) + ∫ y in Ioi t, (y + t) * logistic y)) := by
    ring
  rw [this, hIoi, hfull, hval]
  ring

/-- The basic kernel integral `F₁(t) = ∫₀^∞ x H(x,t) dx = t²/2 + 2π²/3`. -/
lemma integral_mirzKernel (t : ℝ) :
    ∫ x in Ioi (0:ℝ), x * mirzKernel x t = t ^ 2 / 2 + 2 * π ^ 2 / 3 := by
  rcases le_or_gt 0 t with ht | ht
  · exact integral_mirzKernel_of_nonneg ht
  · have h := integral_mirzKernel_of_nonneg (t := -t) (by linarith)
    rw [show ((-t) ^ 2 : ℝ) = t ^ 2 by ring] at h
    rw [← h]
    exact setIntegral_congr_fun measurableSet_Ioi (fun x _ => by rw [mirzKernel_neg])

/-- `x ↦ x · H(x, s)` is integrable on the positive half-line. -/
lemma integrableOn_lin_mul_mirzKernel (s : ℝ) :
    IntegrableOn (fun x => x * mirzKernel x s) (Ioi 0) volume := by
  have iA : IntegrableOn (fun x => x * logistic (x + s)) (Ioi 0) volume := by
    simpa using integrableOn_affine_mul_logistic 0 1 0 s
  have iB : IntegrableOn (fun x => x * logistic (x + -s)) (Ioi 0) volume := by
    simpa using integrableOn_affine_mul_logistic 0 1 0 (-s)
  have iAB : IntegrableOn (fun x => x * logistic (x + s) + x * logistic (x + -s))
      (Ioi 0) volume := iA.add iB
  refine iAB.congr_fun (fun x _ => ?_) measurableSet_Ioi
  rw [mirzKernel_eq, sub_eq_add_neg]
  ring

/-! ## The main statement -/

/--
**Mirzakhani's recursion for Weil–Petersson volumes: base cases and reduction.**

With `H` Mirzakhani's integration kernel, the recursion reads
`∂_{L₁} (L₁ V_{g,n}(L)) = (1/2) ∫∫ x y H(x+y, L₁) P(x,y,L̂) dx dy
   + Σ_{k≥2} (1/2) ∫ x (H(x, L₁+L_k) + H(x, L₁-L_k)) V_{g,n-1}(x, L̂) dx`.

We verify:
* the base case `V_{0,3} = 1`;
* the `(g,n) = (1,1)` instance of the recursion: here the pair of pants obtained by cutting a
  one-holed torus has its two remaining boundary components glued to each other, and the term
  carries the factor `1/4 = (1/2)·(1/2)` coming from the elliptic involution and from the
  interchangeability of the two ends of the cut curve, so the recursion reads
  `∂_L (L V_{1,1}(L)) = (1/2) · (1/4) · ∫₀^∞ x H(x, L) dx`, for `V_{1,1}(L) = (L² + 4π²)/48`;
* the `(g,n) = (0,4)` instance of the recursion (here the `P`-term vanishes, since no
  stable splitting exists), for `V_{0,4}(L) = 2π² + (Σ L_i²)/2`;
* a Lean-checked reduction: the `(1,1)` recursion together with the kernel integral
  *determines* `V_{1,1}` uniquely.
-/
theorem mirzakhani_WP_volume :
    (∀ L₁ L₂ L₃ : ℝ, V03 L₁ L₂ L₃ = 1) ∧
    (∀ L : ℝ, HasDerivAt (fun t => t * V11 t)
        ((1 / 2) * ((1 / 4) * ∫ x in Ioi (0:ℝ), x * mirzKernel x L)) L) ∧
    (∀ L₁ L₂ L₃ L₄ : ℝ, HasDerivAt (fun t => t * V04 t L₂ L₃ L₄)
        ((1 / 2) * ∫ x in Ioi (0:ℝ), x *
            ((mirzKernel x (L₁ + L₂) + mirzKernel x (L₁ - L₂)) * V03 x L₃ L₄ +
             (mirzKernel x (L₁ + L₃) + mirzKernel x (L₁ - L₃)) * V03 x L₂ L₄ +
             (mirzKernel x (L₁ + L₄) + mirzKernel x (L₁ - L₄)) * V03 x L₂ L₃)) L₁) ∧
    (∀ W : ℝ → ℝ,
      (∀ L : ℝ, HasDerivAt (fun t => t * W t)
        ((1 / 2) * ((1 / 4) * ∫ x in Ioi (0:ℝ), x * mirzKernel x L)) L) →
      ∀ L : ℝ, L ≠ 0 → W L = V11 L) := by
  have I := integrableOn_lin_mul_mirzKernel
  -- the `(1,1)` recursion
  have part2 : ∀ L : ℝ, HasDerivAt (fun t => t * V11 t)
      ((1 / 2) * ((1 / 4) * ∫ x in Ioi (0:ℝ), x * mirzKernel x L)) L := by
    intro L
    have hfun : (fun t : ℝ => t * V11 t) = fun t => (t ^ 3 + 4 * π ^ 2 * t) / 48 := by
      funext t; unfold V11; ring
    have h1 : HasDerivAt (fun t : ℝ => t ^ 3 + 4 * π ^ 2 * t) (3 * L ^ 2 + 4 * π ^ 2) L := by
      simpa using (hasDerivAt_pow 3 L).add ((hasDerivAt_id L).const_mul (4 * π ^ 2))
    have hd : HasDerivAt (fun t : ℝ => (t ^ 3 + 4 * π ^ 2 * t) / 48)
        ((3 * L ^ 2 + 4 * π ^ 2) / 48) L := h1.div_const 48
    rw [hfun, integral_mirzKernel]
    convert hd using 1
    ring
  refine ⟨fun _ _ _ => rfl, part2, ?_, ?_⟩
  · -- the `(0,4)` recursion
    intro L₁ L₂ L₃ L₄
    have hfun : (fun t : ℝ => t * V04 t L₂ L₃ L₄)
        = fun t => 2 * π ^ 2 * t + (t ^ 3 + (L₂ ^ 2 + L₃ ^ 2 + L₄ ^ 2) * t) / 2 := by
      funext t; unfold V04; ring
    have h1 : HasDerivAt (fun t : ℝ => t ^ 3 + (L₂ ^ 2 + L₃ ^ 2 + L₄ ^ 2) * t)
        (3 * L₁ ^ 2 + (L₂ ^ 2 + L₃ ^ 2 + L₄ ^ 2)) L₁ := by
      simpa using (hasDerivAt_pow 3 L₁).add
        ((hasDerivAt_id L₁).const_mul (L₂ ^ 2 + L₃ ^ 2 + L₄ ^ 2))
    have h2 : HasDerivAt (fun t : ℝ => 2 * π ^ 2 * t) (2 * π ^ 2) L₁ := by
      simpa using (hasDerivAt_id L₁).const_mul (2 * π ^ 2)
    have hd : HasDerivAt (fun t : ℝ => 2 * π ^ 2 * t
        + (t ^ 3 + (L₂ ^ 2 + L₃ ^ 2 + L₄ ^ 2) * t) / 2)
        (2 * π ^ 2 + (3 * L₁ ^ 2 + (L₂ ^ 2 + L₃ ^ 2 + L₄ ^ 2)) / 2) L₁ :=
      h2.add (h1.div_const 2)
    have hpt : ∀ x : ℝ, x *
        ((mirzKernel x (L₁ + L₂) + mirzKernel x (L₁ - L₂)) * V03 x L₃ L₄ +
         (mirzKernel x (L₁ + L₃) + mirzKernel x (L₁ - L₃)) * V03 x L₂ L₄ +
         (mirzKernel x (L₁ + L₄) + mirzKernel x (L₁ - L₄)) * V03 x L₂ L₃)
        = ((x * mirzKernel x (L₁ + L₂) + x * mirzKernel x (L₁ - L₂))
            + (x * mirzKernel x (L₁ + L₃) + x * mirzKernel x (L₁ - L₃)))
          + (x * mirzKernel x (L₁ + L₄) + x * mirzKernel x (L₁ - L₄)) := by
      intro x; simp only [V03]; ring
    have hI : ∫ x in Ioi (0:ℝ), x *
        ((mirzKernel x (L₁ + L₂) + mirzKernel x (L₁ - L₂)) * V03 x L₃ L₄ +
         (mirzKernel x (L₁ + L₃) + mirzKernel x (L₁ - L₃)) * V03 x L₂ L₄ +
         (mirzKernel x (L₁ + L₄) + mirzKernel x (L₁ - L₄)) * V03 x L₂ L₃)
        = (((L₁ + L₂) ^ 2 / 2 + 2 * π ^ 2 / 3) + ((L₁ - L₂) ^ 2 / 2 + 2 * π ^ 2 / 3))
          + (((L₁ + L₃) ^ 2 / 2 + 2 * π ^ 2 / 3) + ((L₁ - L₃) ^ 2 / 2 + 2 * π ^ 2 / 3))
          + (((L₁ + L₄) ^ 2 / 2 + 2 * π ^ 2 / 3) + ((L₁ - L₄) ^ 2 / 2 + 2 * π ^ 2 / 3)) := by
      have J : ∀ a b : ℝ, IntegrableOn
          (fun x : ℝ => x * mirzKernel x a + x * mirzKernel x b) (Ioi 0) volume :=
        fun a b => (I a).add (I b)
      have J2 : IntegrableOn (fun x : ℝ =>
          (x * mirzKernel x (L₁ + L₂) + x * mirzKernel x (L₁ - L₂))
            + (x * mirzKernel x (L₁ + L₃) + x * mirzKernel x (L₁ - L₃))) (Ioi 0) volume :=
        (J _ _).add (J _ _)
      rw [setIntegral_congr_fun measurableSet_Ioi (fun x _ => hpt x),
        integral_add J2 (J (L₁ + L₄) (L₁ - L₄)),
        integral_add (J (L₁ + L₂) (L₁ - L₂)) (J (L₁ + L₃) (L₁ - L₃)),
        integral_add (I (L₁ + L₂)) (I (L₁ - L₂)),
        integral_add (I (L₁ + L₃)) (I (L₁ - L₃)),
        integral_add (I (L₁ + L₄)) (I (L₁ - L₄)),
        integral_mirzKernel, integral_mirzKernel, integral_mirzKernel,
        integral_mirzKernel, integral_mirzKernel, integral_mirzKernel]
    rw [hfun, hI]
    convert hd using 1
    ring
  · -- uniqueness: the recursion determines `V₁₁`
    intro W hW L hL
    have hd : ∀ x : ℝ, HasDerivAt (fun t => t * W t - t * V11 t) 0 x := by
      intro x; simpa using (hW x).sub (part2 x)
    have hdiff : Differentiable ℝ (fun t => t * W t - t * V11 t) :=
      fun x => (hd x).differentiableAt
    have hderiv : ∀ x, deriv (fun t => t * W t - t * V11 t) x = 0 := fun x => (hd x).deriv
    have h0 := is_const_of_deriv_eq_zero hdiff hderiv L 0
    simp only [zero_mul, sub_self] at h0
    exact mul_left_cancel₀ hL (by linarith)

end Frontier

