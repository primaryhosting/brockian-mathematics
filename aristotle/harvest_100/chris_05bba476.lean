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

namespace Frontier

open MeasureTheory Set Real

/-! ## Mirzakhani's integration kernel

Mirzakhani's recursion for Weil–Petersson volumes of moduli spaces of bordered
hyperbolic surfaces is driven by the kernel

`H (x, t) = 1 / (1 + exp ((x + t) / 2)) + 1 / (1 + exp ((x - t) / 2))`.

We write `wpPhi u = 1 / (1 + exp (u / 2))`, so that `H (x, t) = wpPhi (x+t) + wpPhi (x-t)`.
-/

/-- The basic Fermi–Dirac type profile `u ↦ 1 / (1 + e^{u/2})` out of which Mirzakhani's
integration kernel is built. -/
noncomputable def wpPhi (u : ℝ) : ℝ := 1 / (1 + Real.exp (u / 2))

/-- Mirzakhani's integration kernel `H (x, t)`. -/
noncomputable def mirzakhaniH (x t : ℝ) : ℝ := wpPhi (x + t) + wpPhi (x - t)

/-- Weil–Petersson volume of the moduli space of hyperbolic pairs of pants: `V_{0,3} = 1`. -/
def wpV03 (_L₁ _L₂ _L₃ : ℝ) : ℝ := 1

/-- Weil–Petersson volume polynomial of `M_{0,4}`. -/
noncomputable def wpV04 (L₁ L₂ L₃ L₄ : ℝ) : ℝ :=
  2 * Real.pi ^ 2 + (L₁ ^ 2 + L₂ ^ 2 + L₃ ^ 2 + L₄ ^ 2) / 2

/-- Weil–Petersson volume polynomial of `M_{1,1}` (in the normalisation in which the
elliptic involution is *not* quotiented out). -/
noncomputable def wpV11 (L : ℝ) : ℝ := L ^ 2 / 24 + Real.pi ^ 2 / 6

/-! ## Elementary properties of the kernel -/

theorem continuous_wpPhi : Continuous wpPhi := by
  unfold wpPhi
  apply Continuous.div continuous_const
  · exact continuous_const.add (Real.continuous_exp.comp (continuous_id.div_const 2))
  · intro u
    positivity

theorem wpPhi_pos (u : ℝ) : 0 < wpPhi u := by
  unfold wpPhi
  positivity

theorem wpPhi_le_exp (u : ℝ) : wpPhi u ≤ Real.exp (-(u / 2)) := by
  unfold wpPhi
  rw [Real.exp_neg, one_div]
  apply inv_anti₀ (Real.exp_pos _)
  linarith [Real.exp_pos (u/2)]

theorem wpPhi_add_neg (u : ℝ) : wpPhi u + wpPhi (-u) = 1 := by
  unfold wpPhi
  have h1 : (0:ℝ) < Real.exp (u/2) := Real.exp_pos _
  have h2 : Real.exp (-u/2) = (Real.exp (u/2))⁻¹ := by
    rw [← Real.exp_neg]; congr 1; ring
  rw [h2]
  field_simp
  ring

/-! ## Integrability -/

theorem integrableOn_wpPhi_Ioi (c : ℝ) : IntegrableOn wpPhi (Ioi c) := by
  have hg : IntegrableOn (fun u : ℝ => Real.exp (-(1/2) * u)) (Ioi c) :=
    exp_neg_integrableOn_Ioi c (by norm_num)
  apply Integrable.mono' hg continuous_wpPhi.aestronglyMeasurable
  filter_upwards with u
  rw [Real.norm_eq_abs, abs_of_pos (wpPhi_pos u)]
  have := wpPhi_le_exp u
  rw [show -(1/2 : ℝ) * u = -(u/2) by ring]
  exact this

theorem integrableOn_id_mul_wpPhi_Ioi_zero :
    IntegrableOn (fun u : ℝ => u * wpPhi u) (Ioi 0) := by
  have hg : IntegrableOn (fun u : ℝ => u * Real.exp (-((1/2) * u))) (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := 1) (p := 1) (b := (1/2 : ℝ))
      (by norm_num) (le_refl 1) (by norm_num)
    apply h.congr_fun _ measurableSet_Ioi
    intro x hx
    simp [Real.rpow_one]
  have hmeas : Continuous (fun u : ℝ => u * wpPhi u) := continuous_id.mul continuous_wpPhi
  apply Integrable.mono' hg hmeas.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  simp only [mem_Ioi] at hu
  rw [Real.norm_eq_abs, abs_of_pos (mul_pos hu (wpPhi_pos u))]
  have h1 := wpPhi_le_exp u
  have h3 : u * wpPhi u ≤ u * Real.exp (-(u/2)) := by nlinarith [wpPhi_pos u]
  rw [show -((1/2 : ℝ) * u) = -(u/2) by ring]
  exact h3

theorem integrableOn_id_mul_wpPhi_Ioi (c : ℝ) :
    IntegrableOn (fun u : ℝ => u * wpPhi u) (Ioi c) := by
  rcases le_or_gt 0 c with h | h
  · exact integrableOn_id_mul_wpPhi_Ioi_zero.mono_set (Ioi_subset_Ioi h)
  · have h1 : IntegrableOn (fun u : ℝ => u * wpPhi u) (Ioc c 0) :=
      (continuous_id.mul continuous_wpPhi).integrableOn_Ioc
    have h2 := h1.union integrableOn_id_mul_wpPhi_Ioi_zero
    rwa [Ioc_union_Ioi_eq_Ioi h.le] at h2

theorem integrableOn_id_mul_wpPhi_shift (s : ℝ) :
    IntegrableOn (fun x : ℝ => x * wpPhi (x + s)) (Ioi 0) := by
  have hg : IntegrableOn (fun u : ℝ => Real.exp (-(s/2)) * (u * Real.exp (-((1/2) * u))))
      (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := 1) (p := 1) (b := (1/2 : ℝ))
      (by norm_num) (le_refl 1) (by norm_num)
    have h' : IntegrableOn (fun u : ℝ => u * Real.exp (-((1/2) * u))) (Ioi 0) := by
      apply h.congr_fun _ measurableSet_Ioi
      intro x hx
      simp [Real.rpow_one]
    exact h'.const_mul _
  have hmeas : Continuous (fun x : ℝ => x * wpPhi (x + s)) :=
    continuous_id.mul (continuous_wpPhi.comp (continuous_id.add continuous_const))
  apply Integrable.mono' hg hmeas.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  simp only [mem_Ioi] at hu
  rw [Real.norm_eq_abs, abs_of_pos (mul_pos hu (wpPhi_pos _))]
  have h1 : wpPhi (u + s) ≤ Real.exp (-((u+s)/2)) := wpPhi_le_exp _
  have h2 : Real.exp (-((u+s)/2)) = Real.exp (-(s/2)) * Real.exp (-((1/2) * u)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [h2] at h1
  nlinarith [wpPhi_pos (u+s), Real.exp_pos (-(s/2)), Real.exp_pos (-((1/2)*u))]

theorem integrableOn_id_mul_H (t : ℝ) :
    IntegrableOn (fun x : ℝ => x * mirzakhaniH x t) (Ioi 0) := by
  have h1 := integrableOn_id_mul_wpPhi_shift t
  have h2 := integrableOn_id_mul_wpPhi_shift (-t)
  have h3 : IntegrableOn (fun x : ℝ => x * wpPhi (x + t) + x * wpPhi (x + -t)) (Ioi 0) :=
    h1.add h2
  apply MeasureTheory.IntegrableOn.congr_fun h3 _ measurableSet_Ioi
  intro x _
  show x * wpPhi (x + t) + x * wpPhi (x + -t) = x * mirzakhaniH x t
  unfold mirzakhaniH
  rw [show x - t = x + -t from by ring]
  ring

/-! ## The two basic definite integrals -/

theorem intOn_id_exp (r : ℝ) (hr : 0 < r) :
    IntegrableOn (fun x : ℝ => x * Real.exp (-(r * x))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := 1) (p := 1) (b := r)
    (by norm_num) (le_refl 1) hr
  apply h.congr_fun _ measurableSet_Ioi
  intro x hx
  simp [Real.rpow_one]

theorem int_id_exp (r : ℝ) (hr : 0 < r) :
    ∫ x in Ioi (0:ℝ), x * Real.exp (-(r * x)) = 1 / r ^ 2 := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := r) (by norm_num) hr
  rw [Real.Gamma_two] at h
  have e : ∫ x in Ioi (0:ℝ), x * Real.exp (-(r * x))
      = ∫ t in Ioi (0:ℝ), t ^ ((2:ℝ) - 1) * Real.exp (-(r * t)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    norm_num
  rw [e, h, mul_one, one_div]
  simp

/-- The alternating Basel series `∑ (-1)^n / (n+1)^2 = π^2/12`. -/
theorem altBasel : HasSum (fun n : ℕ => (-1:ℝ) ^ n / ((n:ℝ) + 1) ^ 2) (Real.pi ^ 2 / 12) := by
  have hS : HasSum (fun n : ℕ => 1 / ((n:ℝ)) ^ 2) (Real.pi ^ 2 / 6) := hasSum_zeta_two
  have hE : HasSum (fun k : ℕ => 1 / (((2 * k : ℕ)) : ℝ) ^ 2) (Real.pi ^ 2 / 24) := by
    have h4 := hS.mul_left (1 / 4)
    have he : (fun i : ℕ => (1:ℝ) / 4 * (1 / (i:ℝ) ^ 2))
        = fun k : ℕ => 1 / (((2 * k : ℕ)) : ℝ) ^ 2 := by
      funext k; push_cast; ring
    rw [he] at h4
    convert h4 using 1; ring
  have hOs : Summable (fun k : ℕ => 1 / (((2 * k + 1 : ℕ)) : ℝ) ^ 2) := by
    have hinj : Function.Injective (fun k : ℕ => 2 * k + 1) := by
      intro a b h; simp only [] at h; omega
    exact hS.summable.comp_injective hinj
  have h := HasSum.even_add_odd (f := fun n : ℕ => 1 / ((n:ℝ)) ^ 2) hE hOs.hasSum
  have hval : Real.pi ^ 2 / 24 + (∑' k : ℕ, 1 / (((2 * k + 1 : ℕ)) : ℝ) ^ 2) = Real.pi ^ 2 / 6 :=
    (hS.unique h).symm
  have hO : HasSum (fun k : ℕ => 1 / (((2 * k + 1 : ℕ)) : ℝ) ^ 2) (Real.pi ^ 2 / 8) := by
    have he : (∑' k : ℕ, 1 / (((2 * k + 1 : ℕ)) : ℝ) ^ 2) = Real.pi ^ 2 / 8 := by linarith
    exact he ▸ hOs.hasSum
  set g : ℕ → ℝ := fun m => -((-1:ℝ) ^ m) / (m:ℝ) ^ 2 with hg
  have h0 : g 0 = 0 := by simp [hg]
  have hgE : HasSum (fun k : ℕ => g (2 * k)) (-(Real.pi ^ 2 / 24)) := by
    have h1 := hE.mul_left (-1)
    have he : (fun k : ℕ => (-1:ℝ) * (1 / (((2 * k : ℕ)) : ℝ) ^ 2)) = fun k : ℕ => g (2 * k) := by
      funext k; simp only [hg, pow_mul]; push_cast; ring
    rw [he] at h1
    convert h1 using 1; ring
  have hgO : HasSum (fun k : ℕ => g (2 * k + 1)) (Real.pi ^ 2 / 8) := by
    have he : (fun k : ℕ => 1 / (((2 * k + 1 : ℕ)) : ℝ) ^ 2) = fun k : ℕ => g (2 * k + 1) := by
      funext k; simp only [hg, pow_succ, pow_mul]; push_cast; ring
    rw [he] at hO
    exact hO
  have hgsum : HasSum g ((-(Real.pi ^ 2 / 24) + Real.pi ^ 2 / 8) + ∑ i ∈ Finset.range 1, g i) := by
    simpa [h0] using hgE.even_add_odd hgO
  have hshift := (hasSum_nat_add_iff (f := g) 1).2 hgsum
  have he2 : (fun n : ℕ => g (n + 1)) = fun n : ℕ => (-1:ℝ) ^ n / ((n:ℝ) + 1) ^ 2 := by
    funext n; simp only [hg, pow_succ]; push_cast; ring
  rw [he2] at hshift
  convert hshift using 1
  ring

theorem wpPhi_series (u : ℝ) (hu : 0 < u) :
    wpPhi u = ∑' n : ℕ, (-1:ℝ) ^ n * Real.exp (-(((n:ℝ) + 1) / 2 * u)) := by
  unfold wpPhi
  have hr : ‖(-Real.exp (-(u / 2)))‖ < 1 := by
    rw [norm_neg, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]
    linarith
  have hg := hasSum_geometric_of_norm_lt_one hr
  have h2 := hg.mul_left (Real.exp (-(u / 2)))
  have he : (fun n : ℕ => Real.exp (-(u / 2)) * (-Real.exp (-(u / 2))) ^ n)
      = fun n : ℕ => (-1:ℝ) ^ n * Real.exp (-(((n:ℝ) + 1) / 2 * u)) := by
    funext n
    have h1 : Real.exp (-(u / 2)) * Real.exp ((n:ℝ) * -(u / 2))
        = Real.exp (-(((n:ℝ) + 1) / 2 * u)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [neg_pow, ← Real.exp_nat_mul, ← mul_assoc, mul_comm (Real.exp (-(u / 2))) ((-1:ℝ) ^ n),
      mul_assoc, h1]
  rw [he] at h2
  rw [h2.tsum_eq, Real.exp_neg]
  have hp : (0:ℝ) < Real.exp (u / 2) := Real.exp_pos _
  field_simp
  rw [show Real.exp (u / 2) - -1 = 1 + Real.exp (u / 2) from by ring, div_self (by positivity)]

/-- The key definite integral: `∫_0^∞ u / (1 + e^{u/2}) du = π²/3`. -/
theorem int_id_mul_wpPhi : (∫ u in Ioi (0:ℝ), u * wpPhi u) = Real.pi ^ 2 / 3 := by
  set F : ℕ → ℝ → ℝ := fun n u => (-1:ℝ) ^ n * (u * Real.exp (-(((n:ℝ) + 1) / 2 * u))) with hF
  have hpos : ∀ n : ℕ, (0:ℝ) < ((n:ℝ) + 1) / 2 := by intro n; positivity
  have hint : ∀ n : ℕ, Integrable (F n) (volume.restrict (Ioi 0)) := fun n =>
    (intOn_id_exp _ (hpos n)).const_mul ((-1:ℝ) ^ n)
  have hnorm : ∀ n : ℕ, ∫ u in Ioi (0:ℝ), ‖F n u‖ = 4 / ((n:ℝ) + 1) ^ 2 := by
    intro n
    have e : ∫ u in Ioi (0:ℝ), ‖F n u‖
        = ∫ u in Ioi (0:ℝ), u * Real.exp (-(((n:ℝ) + 1) / 2 * u)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      simp only [mem_Ioi] at hx
      rw [hF]
      simp only []
      rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_mul,
        Real.norm_eq_abs, abs_of_pos hx, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [e, int_id_exp _ (hpos n)]
    field_simp
    ring
  have hsum : Summable (fun n : ℕ => ∫ u in Ioi (0:ℝ), ‖F n u‖) := by
    have hs : Summable (fun n : ℕ => 4 / ((n:ℝ) + 1) ^ 2) := by
      have h1 := (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
      have h2 := ((summable_nat_add_iff 1).2 h1).mul_left 4
      apply h2.congr
      intro n
      push_cast
      ring
    exact hs.congr (fun n => (hnorm n).symm)
  have key := integral_tsum_of_summable_integral_norm (F := F) hint hsum
  have hL : ∑' (n : ℕ), ∫ u in Ioi (0:ℝ), F n u = Real.pi ^ 2 / 3 := by
    have e : ∀ n : ℕ, (∫ u in Ioi (0:ℝ), F n u) = 4 * ((-1:ℝ) ^ n / ((n:ℝ) + 1) ^ 2) := by
      intro n
      rw [hF]
      simp only []
      rw [integral_const_mul, int_id_exp _ (hpos n)]
      field_simp
      ring
    rw [tsum_congr e, (altBasel.mul_left 4).tsum_eq]
    ring
  have hR : (∫ u in Ioi (0:ℝ), ∑' (n : ℕ), F n u) = ∫ u in Ioi (0:ℝ), u * wpPhi u := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    simp only [mem_Ioi] at hu
    show ∑' (n : ℕ), F n u = u * wpPhi u
    rw [wpPhi_series u hu, ← tsum_mul_left]
    apply tsum_congr
    intro n
    rw [hF]
    ring
  rw [← hR, ← key, hL]

/-! ## Mirzakhani's kernel integral `F₁` -/

theorem setIntegral_Ioi_comp_add (f : ℝ → ℝ) (a t : ℝ) :
    ∫ x in Ioi a, f (x + t) = ∫ y in Ioi (a + t), f y := by
  have h := (measurePreserving_add_right volume t).setIntegral_preimage_emb
    (measurableEmbedding_addRight t) f (Ioi (a + t))
  rw [show (fun x => x + t) ⁻¹' (Ioi (a + t)) = Ioi a from by ext x; simp] at h
  exact h

/-- `∫_0^∞ x φ(x+s) dx = ∫_s^∞ u φ(u) du - s ∫_s^∞ φ(u) du`. -/
theorem int_id_mul_wpPhi_shift (s : ℝ) :
    (∫ x in Ioi (0:ℝ), x * wpPhi (x + s))
      = (∫ u in Ioi s, u * wpPhi u) - s * ∫ u in Ioi s, wpPhi u := by
  have h1 : (∫ x in Ioi (0:ℝ), x * wpPhi (x + s))
      = ∫ x in Ioi (0:ℝ), ((fun y : ℝ => (y - s) * wpPhi y) (x + s)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    simp only []
    ring_nf
  rw [h1, setIntegral_Ioi_comp_add (fun y : ℝ => (y - s) * wpPhi y) 0 s, zero_add]
  have h2 : ∀ y : ℝ, (y - s) * wpPhi y = y * wpPhi y - s * wpPhi y := by intro y; ring
  simp only [h2]
  rw [integral_sub (integrableOn_id_mul_wpPhi_Ioi s) ((integrableOn_wpPhi_Ioi s).const_mul s),
    integral_const_mul]

/-- Reflection: `∫_{-t}^{t} φ = t`. -/
theorem intervalIntegral_wpPhi_symm (t : ℝ) :
    (∫ u in (-t)..t, wpPhi u) = t := by
  have hint1 : IntervalIntegrable (fun u : ℝ => wpPhi (-u)) volume 0 t :=
    (continuous_wpPhi.comp continuous_neg).intervalIntegrable _ _
  have hint2 : IntervalIntegrable wpPhi volume 0 t := continuous_wpPhi.intervalIntegrable _ _
  have hsplit : (∫ u in (-t)..t, wpPhi u)
      = (∫ u in (-t)..(0:ℝ), wpPhi u) + ∫ u in (0:ℝ)..t, wpPhi u := by
    rw [intervalIntegral.integral_add_adjacent_intervals]
    · exact continuous_wpPhi.intervalIntegrable _ _
    · exact continuous_wpPhi.intervalIntegrable _ _
  have hrefl : (∫ u in (-t)..(0:ℝ), wpPhi u) = ∫ u in (0:ℝ)..t, wpPhi (-u) := by
    rw [intervalIntegral.integral_comp_neg (fun u => wpPhi u)]
    simp
  have hadd : (∫ u in (0:ℝ)..t, wpPhi (-u)) + ∫ u in (0:ℝ)..t, wpPhi u
      = ∫ u in (0:ℝ)..t, (wpPhi (-u) + wpPhi u) :=
    (intervalIntegral.integral_add hint1 hint2).symm
  have hone : ∀ u : ℝ, wpPhi (-u) + wpPhi u = 1 := by
    intro u; rw [add_comm]; exact wpPhi_add_neg u
  rw [hsplit, hrefl, hadd]
  simp only [hone]
  simp

/-- Reflection for the weighted kernel: `∫_{-t}^{t} u φ(u) du = 2 ∫_0^t u φ(u) du - t²/2`. -/
theorem intervalIntegral_id_mul_wpPhi_symm (t : ℝ) :
    (∫ u in (-t)..t, u * wpPhi u) = 2 * (∫ u in (0:ℝ)..t, u * wpPhi u) - t ^ 2 / 2 := by
  have hcont : Continuous (fun u : ℝ => u * wpPhi u) := continuous_id.mul continuous_wpPhi
  have hsplit : (∫ u in (-t)..t, u * wpPhi u)
      = (∫ u in (-t)..(0:ℝ), u * wpPhi u) + ∫ u in (0:ℝ)..t, u * wpPhi u := by
    rw [intervalIntegral.integral_add_adjacent_intervals]
    · exact hcont.intervalIntegrable _ _
    · exact hcont.intervalIntegrable _ _
  have hrefl : (∫ u in (-t)..(0:ℝ), u * wpPhi u) = ∫ u in (0:ℝ)..t, (-u) * wpPhi (-u) := by
    rw [intervalIntegral.integral_comp_neg (fun u => u * wpPhi u)]
    simp
  have hpt : ∀ u : ℝ, (-u) * wpPhi (-u) = u * wpPhi u - u := by
    intro u
    have h0 := wpPhi_add_neg u
    have h : wpPhi (-u) = 1 - wpPhi u := by linarith
    rw [h]; ring
  have hsub : (∫ u in (0:ℝ)..t, (u * wpPhi u - u))
      = (∫ u in (0:ℝ)..t, u * wpPhi u) - ∫ u in (0:ℝ)..t, u :=
    intervalIntegral.integral_sub (hcont.intervalIntegrable _ _)
      (continuous_id.intervalIntegrable _ _)
  rw [hsplit, hrefl]
  simp only [hpt]
  rw [hsub, integral_id]
  ring

/-- Splitting an integral over `Ioi a` at a point `b ≥ a`. -/
theorem setIntegral_Ioi_split (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (h1 : IntegrableOn f (Ioc a b)) (h2 : IntegrableOn f (Ioi b)) :
    (∫ u in Ioi a, f u) = (∫ u in a..b, f u) + ∫ u in Ioi b, f u := by
  have hdisj : Disjoint (Ioc a b) (Ioi b) := by
    rw [Set.disjoint_left]
    intro x hx hx2
    exact absurd hx.2 (not_le.mpr hx2)
  have h := setIntegral_union hdisj measurableSet_Ioi h1 h2
  rw [Ioc_union_Ioi_eq_Ioi hab] at h
  rw [h, intervalIntegral.integral_of_le hab]

theorem int_id_mul_mirzakhaniH_nonneg (t : ℝ) (ht : 0 ≤ t) :
    (∫ x in Ioi (0:ℝ), x * mirzakhaniH x t) = t ^ 2 / 2 + 2 * Real.pi ^ 2 / 3 := by
  have hcont : Continuous (fun u : ℝ => u * wpPhi u) := continuous_id.mul continuous_wpPhi
  have hle : (-t : ℝ) ≤ t := by linarith
  -- split the kernel
  have hsplit : (∫ x in Ioi (0:ℝ), x * mirzakhaniH x t)
      = (∫ x in Ioi (0:ℝ), x * wpPhi (x + t)) + ∫ x in Ioi (0:ℝ), x * wpPhi (x + -t) := by
    rw [← integral_add (integrableOn_id_mul_wpPhi_shift t) (integrableOn_id_mul_wpPhi_shift (-t))]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x _
    show x * mirzakhaniH x t = x * wpPhi (x + t) + x * wpPhi (x + -t)
    unfold mirzakhaniH
    rw [show x - t = x + -t from by ring]
    ring
  -- the two shifted integrals
  have e1 := int_id_mul_wpPhi_shift t
  have e2 := int_id_mul_wpPhi_shift (-t)
  -- split the integrals over `Ioi (-t)` at `t`
  have s1 : (∫ u in Ioi (-t), u * wpPhi u)
      = (∫ u in (-t)..t, u * wpPhi u) + ∫ u in Ioi t, u * wpPhi u :=
    setIntegral_Ioi_split _ (-t) t hle hcont.integrableOn_Ioc (integrableOn_id_mul_wpPhi_Ioi t)
  have s2 : (∫ u in Ioi (-t), wpPhi u) = (∫ u in (-t)..t, wpPhi u) + ∫ u in Ioi t, wpPhi u :=
    setIntegral_Ioi_split _ (-t) t hle continuous_wpPhi.integrableOn_Ioc
      (integrableOn_wpPhi_Ioi t)
  have s3 : (∫ u in Ioi (0:ℝ), u * wpPhi u)
      = (∫ u in (0:ℝ)..t, u * wpPhi u) + ∫ u in Ioi t, u * wpPhi u :=
    setIntegral_Ioi_split _ 0 t ht hcont.integrableOn_Ioc (integrableOn_id_mul_wpPhi_Ioi t)
  have r1 := intervalIntegral_wpPhi_symm t
  have r2 := intervalIntegral_id_mul_wpPhi_symm t
  have hbase := int_id_mul_wpPhi
  rw [hsplit, e1, e2, s1, s2, r1, r2] at *
  rw [hbase] at s3
  linarith [s3]

/-- **Mirzakhani's kernel integral.**  For every `t`,
`∫_0^∞ x H(x,t) dx = t²/2 + 2π²/3`. -/
theorem int_id_mul_mirzakhaniH (t : ℝ) :
    (∫ x in Ioi (0:ℝ), x * mirzakhaniH x t) = t ^ 2 / 2 + 2 * Real.pi ^ 2 / 3 := by
  rcases le_or_gt 0 t with h | h
  · exact int_id_mul_mirzakhaniH_nonneg t h
  · have heven : ∀ x : ℝ, mirzakhaniH x t = mirzakhaniH x (-t) := by
      intro x
      unfold mirzakhaniH
      rw [show x + -t = x - t from by ring, show x - -t = x + t from by ring, add_comm]
    have : (∫ x in Ioi (0:ℝ), x * mirzakhaniH x t) = ∫ x in Ioi (0:ℝ), x * mirzakhaniH x (-t) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x _
      show x * mirzakhaniH x t = x * mirzakhaniH x (-t)
      rw [heven x]
    rw [this, int_id_mul_mirzakhaniH_nonneg (-t) (by linarith)]
    ring

/-- The `(0,4)` recursion involves the kernel evaluated at `L₁ + L_k` and `L₁ - L_k`,
weighted by the pair-of-pants volume `V_{0,3} = 1`. -/
theorem int_id_mul_mirzakhaniH_pair (a b c d : ℝ) :
    (∫ x in Ioi (0:ℝ), x * (mirzakhaniH x a + mirzakhaniH x b) * wpV03 x c d)
      = (a ^ 2 / 2 + 2 * Real.pi ^ 2 / 3) + (b ^ 2 / 2 + 2 * Real.pi ^ 2 / 3) := by
  have hcongr : (∫ x in Ioi (0:ℝ), x * (mirzakhaniH x a + mirzakhaniH x b) * wpV03 x c d)
      = ∫ x in Ioi (0:ℝ), (x * mirzakhaniH x a + x * mirzakhaniH x b) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x _
    show x * (mirzakhaniH x a + mirzakhaniH x b) * wpV03 x c d
      = x * mirzakhaniH x a + x * mirzakhaniH x b
    unfold wpV03
    ring
  rw [hcongr, integral_add (integrableOn_id_mul_H a) (integrableOn_id_mul_H b),
    int_id_mul_mirzakhaniH, int_id_mul_mirzakhaniH]

/-! ## The main statement -/

/-- **Mirzakhani's recursion for Weil–Petersson volumes: base case and low-complexity
reductions.**

Mirzakhani's recursion computes the Weil–Petersson volume `V_{g,n}(L₁,…,L_n)` of the moduli
space of bordered hyperbolic surfaces of genus `g` with `n` geodesic boundary components of
lengths `L₁,…,L_n` by integrating the kernel
`H (x, t) = 1/(1 + e^{(x+t)/2}) + 1/(1 + e^{(x-t)/2})`
against volumes of lower complexity.  The four conjuncts below are:

1. the base case `V_{0,3} ≡ 1` (a pair of pants is rigid, so its moduli space is a point);

2. the fundamental kernel integral `∫₀^∞ x H(x,t) dx = t²/2 + 2π²/3`, which is the
   `k = 0` case of Mirzakhani's formula for `F_{2k+1}` and the analytic engine of the whole
   recursion;

3. the `(g,n) = (1,1)` instance of the recursion,
   `∂_L (L · V_{1,1}(L)) = (1/4) ∫₀^∞ x H(x,L) dx`,
   for `V_{1,1}(L) = L²/24 + π²/6`.  Here the coefficient `1/4` is the overall factor `1/2`
   of the recursion times the symmetry factor `1/2` coming from the two ends of the pair of
   pants being glued to each other.  (Both `L²/24 + π²/6` and its half `L²/48 + π²/12` occur
   in the literature, according to whether the elliptic involution of the one-holed torus is
   quotiented out; the two conventions differ by the constant factor `2`, which is absorbed
   into the coefficient of the recursion.)

4. the `(g,n) = (0,4)` instance of the recursion,
   `∂_{L₁}(L₁ · V_{0,4}(L)) = (1/2) Σ_{k=2}^{4} ∫₀^∞ x (H(x, L₁+L_k) + H(x, L₁-L_k)) V_{0,3} dx`,
   for `V_{0,4}(L) = 2π² + (L₁² + L₂² + L₃² + L₄²)/2`.  For `(0,4)` no non-separating or
   separating term occurs (the corresponding surfaces are unstable), so the displayed sum is
   the complete right-hand side of Mirzakhani's recursion in this case. -/
theorem mirzakhani_WP_volume :
    (∀ L₁ L₂ L₃ : ℝ, wpV03 L₁ L₂ L₃ = 1)
  ∧ (∀ t : ℝ, (∫ x in Ioi (0:ℝ), x * mirzakhaniH x t) = t ^ 2 / 2 + 2 * Real.pi ^ 2 / 3)
  ∧ (∀ L : ℝ, HasDerivAt (fun s : ℝ => s * wpV11 s)
        ((1/4) * ∫ x in Ioi (0:ℝ), x * mirzakhaniH x L) L)
  ∧ (∀ L₁ L₂ L₃ L₄ : ℝ, HasDerivAt (fun s : ℝ => s * wpV04 s L₂ L₃ L₄)
        ((1/2) * ((∫ x in Ioi (0:ℝ), x * (mirzakhaniH x (L₁ + L₂) + mirzakhaniH x (L₁ - L₂))
                      * wpV03 x L₃ L₄)
                + (∫ x in Ioi (0:ℝ), x * (mirzakhaniH x (L₁ + L₃) + mirzakhaniH x (L₁ - L₃))
                      * wpV03 x L₂ L₄)
                + (∫ x in Ioi (0:ℝ), x * (mirzakhaniH x (L₁ + L₄) + mirzakhaniH x (L₁ - L₄))
                      * wpV03 x L₂ L₃))) L₁) := by
  refine ⟨fun _ _ _ => rfl, int_id_mul_mirzakhaniH, ?_, ?_⟩
  · intro L
    rw [int_id_mul_mirzakhaniH L]
    have h1 : HasDerivAt (fun s : ℝ => s * (s ^ 2 / 24 + Real.pi ^ 2 / 6))
        (1 * (L ^ 2 / 24 + Real.pi ^ 2 / 6) + L * ((2 : ℕ) * L ^ (2 - 1) / 24)) L :=
      (hasDerivAt_id L).mul (((hasDerivAt_pow 2 L).div_const 24).add_const _)
    have h2 : (fun s : ℝ => s * wpV11 s) = fun s : ℝ => s * (s ^ 2 / 24 + Real.pi ^ 2 / 6) := by
      funext s; unfold wpV11; ring
    rw [h2]
    convert h1 using 1
    push_cast
    ring
  · intro L₁ L₂ L₃ L₄
    rw [int_id_mul_mirzakhaniH_pair, int_id_mul_mirzakhaniH_pair, int_id_mul_mirzakhaniH_pair]
    have h1 : HasDerivAt
        (fun s : ℝ => s * (2 * Real.pi ^ 2 + (s ^ 2 + L₂ ^ 2 + L₃ ^ 2 + L₄ ^ 2) / 2))
        (1 * (2 * Real.pi ^ 2 + (L₁ ^ 2 + L₂ ^ 2 + L₃ ^ 2 + L₄ ^ 2) / 2)
          + L₁ * ((2 : ℕ) * L₁ ^ (2 - 1) / 2)) L₁ :=
      (hasDerivAt_id L₁).mul
        (((((hasDerivAt_pow 2 L₁).add_const (L₂ ^ 2)).add_const (L₃ ^ 2)).add_const
          (L₄ ^ 2)).div_const 2 |>.const_add (2 * Real.pi ^ 2))
    have h2 : (fun s : ℝ => s * wpV04 s L₂ L₃ L₄)
        = fun s : ℝ => s * (2 * Real.pi ^ 2 + (s ^ 2 + L₂ ^ 2 + L₃ ^ 2 + L₄ ^ 2) / 2) := by
      funext s; unfold wpV04; ring
    rw [h2]
    convert h1 using 1
    push_cast
    ring

end Frontier

