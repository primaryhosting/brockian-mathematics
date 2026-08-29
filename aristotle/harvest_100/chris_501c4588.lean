import Mathlib

/-!
# Core of the Mermin–Wagner argument

This file contains the model-independent part of the Mermin–Wagner theorem:
a finite collection of classical `O(2)` spins with an arbitrary nonnegative,
rotation-invariant pair interaction, plus arbitrary single-site terms
(boundary conditions / external fields).

The main result `Phys.abs_magnetization_le` bounds the magnetization at a
distinguished site `o` by the *Dirichlet energy* of any "spin wave" profile
`a : V → ℝ` which equals `π` at `o` and vanishes wherever a single-site term
is present.
-/

open MeasureTheory

noncomputable instance factTwoPi : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- The state space of a single classical `O(2)` (planar rotator) spin. -/
abbrev Spin := AddCircle (2 * Real.pi)

namespace Phys

section Trig

theorem one_sub_cos_le_sq (x : ℝ) : 1 - Real.cos x ≤ x ^ 2 / 2 := by
  have h : Real.cos x = 1 - 2 * Real.sin (x / 2) ^ 2 := by
    have h2 : Real.cos (2 * (x / 2)) = 1 - 2 * Real.sin (x / 2) ^ 2 := by
      rw [Real.cos_two_mul]; nlinarith [Real.sin_sq_add_cos_sq (x / 2)]
    rw [show 2 * (x / 2) = x by ring] at h2; exact h2
  have h3 : |Real.sin (x / 2)| ≤ |x / 2| := Real.abs_sin_le_abs
  nlinarith [sq_abs (Real.sin (x / 2)), sq_abs (x / 2), abs_nonneg (Real.sin (x / 2)),
    abs_nonneg (x / 2)]

theorem angle_abs_cos_le_one (A : Real.Angle) : |A.cos| ≤ 1 := by
  induction A using Real.Angle.induction_on with
  | h x => rw [Real.Angle.cos_coe]; exact Real.abs_cos_le_one x

theorem angle_cos_add_real (A : Real.Angle) (s : ℝ) :
    (A + (s : Real.Angle)).cos = A.cos * Real.cos s - A.sin * Real.sin s := by
  rw [Real.Angle.cos_add, Real.Angle.cos_coe, Real.Angle.sin_coe]

theorem angle_cos_sub_real (A : Real.Angle) (s : ℝ) :
    (A - (s : Real.Angle)).cos = A.cos * Real.cos s + A.sin * Real.sin s := by
  rw [sub_eq_add_neg, ← Real.Angle.coe_neg, angle_cos_add_real]
  simp

/-- The fundamental two-sided ("spin wave") estimate for the rotator interaction. -/
theorem cos_shift_estimate (A : Real.Angle) (s : ℝ) :
    -((A + (s : Real.Angle)).cos + (A - (s : Real.Angle)).cos - 2 * A.cos) ≤ s ^ 2 := by
  rw [angle_cos_add_real, angle_cos_sub_real]
  have h1 : -(A.cos * Real.cos s - A.sin * Real.sin s
      + (A.cos * Real.cos s + A.sin * Real.sin s) - 2 * A.cos)
      = 2 * A.cos * (1 - Real.cos s) := by ring
  rw [h1]
  have h2 : 1 - Real.cos s ≥ 0 := by nlinarith [Real.cos_le_one s]
  have h3 : A.cos ≤ 1 := (abs_le.mp (angle_abs_cos_le_one A)).2
  nlinarith [one_sub_cos_le_sq s]

end Trig

variable {V : Type*} [Fintype V]

/-- The energy of a spin configuration: a rotation-invariant pair interaction with
nonnegative couplings `J`, together with arbitrary single-site terms `G`
(these encode boundary conditions and/or external fields). -/
noncomputable def energy (J : V → V → ℝ) (G : V → Spin → ℝ) (θ : V → Spin) : ℝ :=
  -(∑ x, ∑ y, J x y * Real.Angle.cos (θ x - θ y)) + ∑ x, G x (θ x)

/-- The Dirichlet energy of a spin-wave profile `a`. -/
noncomputable def dirichlet (J : V → V → ℝ) (a : V → ℝ) : ℝ :=
  ∑ x, ∑ y, J x y * (a x - a y) ^ 2

/-- Gibbs expectation of an observable `f` at inverse temperature `β`. -/
noncomputable def gibbsAvg (β : ℝ) (H : (V → Spin) → ℝ) (f : (V → Spin) → ℝ) : ℝ :=
  (∫ θ, f θ * Real.exp (-β * H θ)) / (∫ θ, Real.exp (-β * H θ))

theorem continuous_energy (J : V → V → ℝ) (G : V → Spin → ℝ) (hG : ∀ x, Continuous (G x)) :
    Continuous (energy J G) := by
  unfold energy
  refine Continuous.add (continuous_neg.comp ?_) ?_
  · exact continuous_finset_sum _ fun x _ => continuous_finset_sum _ fun y _ =>
      continuous_const.mul (Real.Angle.continuous_cos.comp
        (((continuous_apply x).sub (continuous_apply y))))
  · exact continuous_finset_sum _ fun x _ => (hG x).comp (continuous_apply x)

theorem integrable_of_continuous {f : (V → Spin) → ℝ} (hf : Continuous f) :
    Integrable f (volume : Measure (V → Spin)) :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

/-- The pointwise two-sided energy estimate: shifting the configuration by `±a`
costs at most the Dirichlet energy of `a`. -/
theorem energy_shift_le (J : V → V → ℝ) (hJ : ∀ x y, 0 ≤ J x y) (G : V → Spin → ℝ)
    (a : V → ℝ) (hGa : ∀ x, a x ≠ 0 → G x = 0) (θ : V → Spin) :
    energy J G (θ + fun x => ((a x : ℝ) : Spin)) + energy J G (θ - fun x => ((a x : ℝ) : Spin))
      - 2 * energy J G θ ≤ dirichlet J a := by
  set sa : V → Spin := fun x => ((a x : ℝ) : Spin) with hsa
  -- single site terms are unchanged
  have hGterm : ∀ x, G x ((θ + sa) x) + G x ((θ - sa) x) - 2 * G x (θ x) = 0 := by
    intro x
    by_cases hx : a x = 0
    · have hz : sa x = 0 := by simp [hsa, hx]
      simp only [Pi.add_apply, Pi.sub_apply, hz, add_zero, sub_zero]; ring
    · simp [hGa x hx]
  have hdiff : ∀ x y, (θ + sa) x - (θ + sa) y = (θ x - θ y) + ((a x - a y : ℝ) : Spin) := by
    intro x y
    show (θ x + sa x) - (θ y + sa y) = _
    rw [AddCircle.coe_sub]
    abel
  have hdiff' : ∀ x y, (θ - sa) x - (θ - sa) y = (θ x - θ y) - ((a x - a y : ℝ) : Spin) := by
    intro x y
    show (θ x - sa x) - (θ y - sa y) = _
    rw [AddCircle.coe_sub]
    abel
  have key : ∀ x y, -(J x y * Real.Angle.cos ((θ + sa) x - (θ + sa) y)
      + J x y * Real.Angle.cos ((θ - sa) x - (θ - sa) y)
      - 2 * (J x y * Real.Angle.cos (θ x - θ y))) ≤ J x y * (a x - a y) ^ 2 := by
    intro x y
    rw [hdiff x y, hdiff' x y]
    have h := cos_shift_estimate (θ x - θ y) (a x - a y)
    calc -(J x y * Real.Angle.cos (θ x - θ y + ((a x - a y : ℝ) : Spin))
            + J x y * Real.Angle.cos (θ x - θ y - ((a x - a y : ℝ) : Spin))
            - 2 * (J x y * Real.Angle.cos (θ x - θ y)))
        = J x y * -(Real.Angle.cos (θ x - θ y + ((a x - a y : ℝ) : Spin))
            + Real.Angle.cos (θ x - θ y - ((a x - a y : ℝ) : Spin))
            - 2 * Real.Angle.cos (θ x - θ y)) := by ring
      _ ≤ J x y * (a x - a y) ^ 2 := mul_le_mul_of_nonneg_left h (hJ x y)
  have hT : (∑ x, G x ((θ + sa) x)) + (∑ x, G x ((θ - sa) x)) - 2 * (∑ x, G x (θ x)) = 0 := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_eq_zero fun x _ => hGterm x
  have hS : (∑ x, ∑ y, J x y * Real.Angle.cos ((θ + sa) x - (θ + sa) y))
      + (∑ x, ∑ y, J x y * Real.Angle.cos ((θ - sa) x - (θ - sa) y))
      - 2 * (∑ x, ∑ y, J x y * Real.Angle.cos (θ x - θ y))
      = ∑ x, ∑ y, (J x y * Real.Angle.cos ((θ + sa) x - (θ + sa) y)
          + J x y * Real.Angle.cos ((θ - sa) x - (θ - sa) y)
          - 2 * (J x y * Real.Angle.cos (θ x - θ y))) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
  unfold energy dirichlet
  have expand : ∀ A B C P Q R : ℝ,
      (-A + P) + (-B + Q) - 2 * (-C + R) = -(A + B - 2 * C) + (P + Q - 2 * R) := by
    intro A B C P Q R; ring
  rw [expand, hT, add_zero, hS, ← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun x _ => ?_
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_le_sum fun y _ => key x y

/-! ### The Gibbs state -/

/-- Translation invariance of the reference measure. -/
theorem integral_shift (F : (V → Spin) → ℝ) (c : V → Spin) :
    ∫ θ, F (θ + c) = ∫ θ, F θ := by
  have h := integral_add_left_eq_self (μ := (volume : Measure (V → Spin))) F c
  rw [← h]
  exact integral_congr_ae (Filter.Eventually.of_forall fun θ => by simp only [add_comm θ c])

/-- The key spin-wave inequality for Gibbs weights. -/
theorem gibbs_shift_ineq {J : V → V → ℝ} {G : V → Spin → ℝ} {β : ℝ} {a : V → ℝ}
    (hJ : ∀ x y, 0 ≤ J x y) (hG : ∀ x, Continuous (G x))
    (hβ : 0 < β) (hGa : ∀ x, a x ≠ 0 → G x = 0)
    (f : (V → Spin) → ℝ) (hf0 : ∀ θ, 0 ≤ f θ) (hfc : Continuous f) :
    (∫ θ, f θ * Real.exp (-β * energy J G θ))
      ≤ Real.exp (β * dirichlet J a / 2) *
          (((∫ θ, f (θ - fun x => ((a x : ℝ) : Spin)) * Real.exp (-β * energy J G θ))
            + ∫ θ, f (θ + fun x => ((a x : ℝ) : Spin)) * Real.exp (-β * energy J G θ)) / 2) := by
  set sa : V → Spin := fun x => ((a x : ℝ) : Spin) with hsa
  set H := energy J G with hH
  have hHc : Continuous H := continuous_energy J G hG
  have hcshift : ∀ c : V → Spin, Continuous fun θ : V → Spin => H (θ + c) :=
    fun c => hHc.comp (continuous_id.add continuous_const)
  -- pointwise inequality
  have hpt : ∀ θ, f θ * Real.exp (-β * H θ)
      ≤ Real.exp (β * dirichlet J a / 2) *
        ((f θ * Real.exp (-β * H (θ + sa)) + f θ * Real.exp (-β * H (θ - sa))) / 2) := by
    intro θ
    have hE := energy_shift_le J hJ G a hGa θ
    set u := H (θ + sa)
    set v := H (θ - sa)
    have hexp : Real.exp (-β * H θ)
        ≤ Real.exp (β * dirichlet J a / 2) * (Real.exp (-β * u / 2) * Real.exp (-β * v / 2)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.2
      nlinarith [hE, hβ]
    have hAM : Real.exp (-β * u / 2) * Real.exp (-β * v / 2)
        ≤ (Real.exp (-β * u) + Real.exp (-β * v)) / 2 := by
      have h1 : Real.exp (-β * u / 2) ^ 2 = Real.exp (-β * u) := by
        rw [sq, ← Real.exp_add]; ring_nf
      have h2 : Real.exp (-β * v / 2) ^ 2 = Real.exp (-β * v) := by
        rw [sq, ← Real.exp_add]; ring_nf
      nlinarith [two_mul_le_add_sq (Real.exp (-β * u / 2)) (Real.exp (-β * v / 2))]
    have hpos : (0:ℝ) < Real.exp (β * dirichlet J a / 2) := Real.exp_pos _
    have hmid : Real.exp (-β * H θ)
        ≤ Real.exp (β * dirichlet J a / 2) * ((Real.exp (-β * u) + Real.exp (-β * v)) / 2) :=
      hexp.trans (mul_le_mul_of_nonneg_left hAM hpos.le)
    calc f θ * Real.exp (-β * H θ)
        ≤ f θ * (Real.exp (β * dirichlet J a / 2) * ((Real.exp (-β * u) + Real.exp (-β * v)) / 2)) :=
          mul_le_mul_of_nonneg_left hmid (hf0 θ)
      _ = Real.exp (β * dirichlet J a / 2) *
            ((f θ * Real.exp (-β * u) + f θ * Real.exp (-β * v)) / 2) := by ring
  -- integrate
  have hc0 : Continuous fun θ : V → Spin => f θ * Real.exp (-β * H θ) :=
    hfc.mul (Real.continuous_exp.comp (continuous_const.mul hHc))
  have hcplus : Continuous fun θ : V → Spin => f θ * Real.exp (-β * H (θ + sa)) :=
    hfc.mul (Real.continuous_exp.comp (continuous_const.mul (hcshift sa)))
  have hcminus : Continuous fun θ : V → Spin => f θ * Real.exp (-β * H (θ - sa)) := by
    have hh : Continuous fun θ : V → Spin => H (θ - sa) := by
      simpa [sub_eq_add_neg] using hcshift (-sa)
    exact hfc.mul (Real.continuous_exp.comp (continuous_const.mul hh))
  have hcRHS : Continuous fun θ : V → Spin => Real.exp (β * dirichlet J a / 2) *
      ((f θ * Real.exp (-β * H (θ + sa)) + f θ * Real.exp (-β * H (θ - sa))) / 2) :=
    continuous_const.mul ((hcplus.add hcminus).div_const 2)
  have hmono := integral_mono (integrable_of_continuous hc0) (integrable_of_continuous hcRHS) hpt
  refine hmono.trans_eq ?_
  rw [integral_const_mul, integral_div, integral_add (integrable_of_continuous hcplus)
    (integrable_of_continuous hcminus)]
  -- change of variables
  have ht1 : (∫ θ, f θ * Real.exp (-β * H (θ + sa)))
      = ∫ θ, f (θ - sa) * Real.exp (-β * H θ) := by
    have h := integral_shift (fun θ : V → Spin => f θ * Real.exp (-β * H (θ + sa))) (-sa)
    rw [← h]
    refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    simp only [← sub_eq_add_neg, sub_add_cancel]
  have ht2 : (∫ θ, f θ * Real.exp (-β * H (θ - sa)))
      = ∫ θ, f (θ + sa) * Real.exp (-β * H θ) := by
    have h := integral_shift (fun θ : V → Spin => f θ * Real.exp (-β * H (θ - sa))) sa
    rw [← h]
    refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    simp only [add_sub_cancel_right]
  rw [ht1, ht2]

theorem dirichlet_nonneg {J : V → V → ℝ} (hJ : ∀ x y, 0 ≤ J x y) (a : V → ℝ) :
    0 ≤ dirichlet J a :=
  Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ =>
    mul_nonneg (hJ x y) (sq_nonneg _)

/-- The partition function is strictly positive. -/
theorem partition_pos {J : V → V → ℝ} {G : V → Spin → ℝ} (hG : ∀ x, Continuous (G x)) (β : ℝ) :
    0 < ∫ θ, Real.exp (-β * energy J G θ) := by
  have hc : Continuous fun θ : V → Spin => Real.exp (-β * energy J G θ) :=
    Real.continuous_exp.comp (continuous_const.mul (continuous_energy J G hG))
  rw [integral_pos_iff_support_of_nonneg (fun θ => (Real.exp_pos _).le)
    (integrable_of_continuous hc)]
  have hsupp : (Function.support fun θ : V → Spin => Real.exp (-β * energy J G θ)) = Set.univ := by
    ext θ; simp [Function.mem_support, (Real.exp_pos _).ne']
  rw [hsupp]
  exact IsOpen.measure_pos volume isOpen_univ Set.univ_nonempty

/-- **Mermin–Wagner bound.**  The magnetization at a site `o` is bounded in terms of the
Dirichlet energy of any spin-wave profile `a` with `a o = π` which vanishes at every site
carrying a single-site (symmetry breaking) term. -/
theorem abs_magnetization_le {J : V → V → ℝ} {G : V → Spin → ℝ} {β : ℝ} {a : V → ℝ}
    (hJ : ∀ x y, 0 ≤ J x y) (hG : ∀ x, Continuous (G x))
    (hβ : 0 < β) (hGa : ∀ x, a x ≠ 0 → G x = 0)
    (o : V) (ho : a o = Real.pi) :
    |gibbsAvg β (energy J G) fun θ => Real.Angle.cos (θ o)|
      ≤ (Real.exp (β * dirichlet J a / 2) - 1) / 2 := by
  set sa : V → Spin := fun x => ((a x : ℝ) : Spin) with hsa
  set H := energy J G with hH
  have hHc : Continuous H := continuous_energy J G hG
  have hexpc : Continuous fun θ : V → Spin => Real.exp (-β * H θ) :=
    Real.continuous_exp.comp (continuous_const.mul hHc)
  have hcosc : Continuous fun θ : V → Spin => Real.Angle.cos (θ o) :=
    Real.Angle.continuous_cos.comp (continuous_apply o)
  set Z : ℝ := ∫ θ, Real.exp (-β * H θ) with hZ
  set C : ℝ := ∫ θ, Real.Angle.cos (θ o) * Real.exp (-β * H θ) with hC
  have hZpos : 0 < Z := partition_pos hG β
  set k : ℝ := Real.exp (β * dirichlet J a / 2) with hk
  have hk1 : 1 ≤ k := by
    rw [hk, show (1:ℝ) = Real.exp 0 by simp]
    refine Real.exp_le_exp.2 ?_
    have := dirichlet_nonneg hJ a
    positivity
  -- shifted values of the observable
  have hsao : sa o = ((Real.pi : ℝ) : Spin) := by rw [hsa]; simp [ho]
  have hshift_sub : ∀ θ : V → Spin, Real.Angle.cos ((θ - sa) o) = -Real.Angle.cos (θ o) := by
    intro θ
    have : (θ - sa) o = θ o - ((Real.pi : ℝ) : Spin) := by
      show θ o - sa o = _; rw [hsao]
    rw [this]; exact Real.Angle.cos_sub_pi _
  have hshift_add : ∀ θ : V → Spin, Real.Angle.cos ((θ + sa) o) = -Real.Angle.cos (θ o) := by
    intro θ
    have : (θ + sa) o = θ o + ((Real.pi : ℝ) : Spin) := by
      show θ o + sa o = _; rw [hsao]
    rw [this]; exact Real.Angle.cos_add_pi _
  -- integrals of `(1 ± cos) * weight`
  have hsplit : ∀ c : ℝ, (∫ θ, (1 + c * Real.Angle.cos (θ o)) * Real.exp (-β * H θ)) = Z + c * C := by
    intro c
    have : ∀ θ : V → Spin, (1 + c * Real.Angle.cos (θ o)) * Real.exp (-β * H θ)
        = Real.exp (-β * H θ) + c * (Real.Angle.cos (θ o) * Real.exp (-β * H θ)) := by
      intro θ; ring
    have hint2 : Integrable
        (fun θ : V → Spin => c * (Real.Angle.cos (θ o) * Real.exp (-β * H θ)))
        (volume : Measure (V → Spin)) :=
      (integrable_of_continuous (hcosc.mul hexpc)).const_mul c
    rw [integral_congr_ae (Filter.Eventually.of_forall this),
      integral_add (integrable_of_continuous hexpc) hint2, integral_const_mul]
  have hkey : ∀ c : ℝ, |c| = 1 → Z + c * C ≤ k * (Z - c * C) := by
    intro c hc
    have hf0 : ∀ θ : V → Spin, 0 ≤ 1 + c * Real.Angle.cos (θ o) := by
      intro θ
      have h1 := angle_abs_cos_le_one (θ o)
      have : |c * Real.Angle.cos (θ o)| ≤ 1 := by
        rw [abs_mul, hc, one_mul]; exact h1
      linarith [(abs_le.mp this).1]
    have hfc : Continuous fun θ : V → Spin => 1 + c * Real.Angle.cos (θ o) :=
      continuous_const.add (continuous_const.mul hcosc)
    have h := gibbs_shift_ineq (a := a) hJ hG hβ hGa
      (fun θ : V → Spin => 1 + c * Real.Angle.cos (θ o)) hf0 hfc
    simp only [← hH, ← hsa] at h
    have e1 : (∫ θ, (1 + c * Real.Angle.cos ((θ - sa) o)) * Real.exp (-β * H θ))
        = Z - c * C := by
      have : ∀ θ : V → Spin, (1 + c * Real.Angle.cos ((θ - sa) o)) * Real.exp (-β * H θ)
          = (1 + (-c) * Real.Angle.cos (θ o)) * Real.exp (-β * H θ) := by
        intro θ; rw [hshift_sub θ]; ring
      rw [integral_congr_ae (Filter.Eventually.of_forall this), hsplit (-c)]; ring
    have e2 : (∫ θ, (1 + c * Real.Angle.cos ((θ + sa) o)) * Real.exp (-β * H θ))
        = Z - c * C := by
      have : ∀ θ : V → Spin, (1 + c * Real.Angle.cos ((θ + sa) o)) * Real.exp (-β * H θ)
          = (1 + (-c) * Real.Angle.cos (θ o)) * Real.exp (-β * H θ) := by
        intro θ; rw [hshift_add θ]; ring
      rw [integral_congr_ae (Filter.Eventually.of_forall this), hsplit (-c)]; ring
    rw [hsplit c, e1, e2] at h
    linarith [h]
  have h1 := hkey 1 (by norm_num)
  have h2 := hkey (-1) (by norm_num)
  have hC1 : C * (k + 1) ≤ Z * (k - 1) := by nlinarith [h1]
  have hC2 : (-C) * (k + 1) ≤ Z * (k - 1) := by nlinarith [h2]
  have habs : |C| * (k + 1) ≤ Z * (k - 1) := by
    rcases abs_cases C with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] <;> assumption
  have heq : |gibbsAvg β H fun θ => Real.Angle.cos (θ o)| = |C| / Z := by
    rw [gibbsAvg, abs_div, abs_of_pos hZpos]
  rw [heq, div_le_iff₀ hZpos]
  nlinarith [habs, abs_nonneg C, mul_nonneg (abs_nonneg C) (sub_nonneg.2 hk1), hZpos.le]

end Phys

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

import RequestProject.Core
import RequestProject.Capacity

/-!
# The nearest-neighbour rotator model on a finite box of `ℤ^d`

We combine the abstract Mermin–Wagner bound of `Core` with the capacity estimate of
`Capacity`: for `d ≤ 2` the Dirichlet energy of the logarithmic spin-wave profile tends
to `0`, uniformly in the size of the box.
-/

open Finset MeasureTheory

namespace Phys

/-- The sites of the box of side `2N+1`, as a type. -/
abbrev Site (d N : ℕ) := {x : Fin d → ℤ // x ∈ box d N}

theorem lnorm_zero (d : ℕ) : lnorm (0 : Fin d → ℤ) = 0 := by
  simp [lnorm]

/-- The origin, viewed as a site of the box. -/
def origin (d N : ℕ) : Site d N := ⟨0, by rw [mem_box, lnorm_zero]; exact Nat.zero_le _⟩

/-- Ferromagnetic nearest-neighbour couplings of strength `Jc`. -/
noncomputable def latJ (d N : ℕ) (Jc : ℝ) : Site d N → Site d N → ℝ :=
  fun x y => if adj x.1 y.1 then Jc else 0

theorem latJ_nonneg {d N : ℕ} {Jc : ℝ} (hJc : 0 ≤ Jc) (x y : Site d N) :
    0 ≤ latJ d N Jc x y := by
  unfold latJ; split <;> simpa using hJc

theorem adj_symm {d : ℕ} {x y : Fin d → ℤ} (h : adj x y) : adj y x := by
  unfold adj at h ⊢
  rw [← h]
  exact Finset.sum_congr rfl fun i _ => by rw [← Int.natAbs_neg]; ring_nf

/-- The pointwise gradient bound for the logarithmic spin-wave profile. -/
theorem swProfile_diff_le {d R : ℕ} (hR : 1 ≤ R) {x y : Fin d → ℤ} (hxy : adj x y) :
    |swProfile d R x - swProfile d R y|
      ≤ Real.pi / (((max (lnorm x) 1 : ℕ) : ℝ) * Real.log ((R : ℝ) + 1)) := by
  have hL : 0 < Real.log ((R : ℝ) + 1) := by
    apply Real.log_pos
    have : (1:ℝ) ≤ (R:ℝ) := by exact_mod_cast hR
    linarith
  have h1 : lnorm y ≤ lnorm x + 1 := adj_lnorm_le hxy
  have h2 : lnorm x ≤ lnorm y + 1 := adj_lnorm_le (adj_symm hxy)
  rcases eq_or_lt_of_le (Nat.zero_le (lnorm x)) with h0 | h0
  · -- `lnorm x = 0`, so `max (lnorm x) 1 = 1`
    have hmax : (max (lnorm x) 1 : ℕ) = 1 := by omega
    rw [hmax]
    have hcast : ((1 : ℕ) : ℝ) = 1 := by norm_num
    rw [hcast, one_mul]
    have hx0 : lnorm x = 0 := by omega
    have hcases : lnorm y = 0 ∨ lnorm y = 1 := by omega
    rcases hcases with hy | hy
    · unfold swProfile
      rw [hx0, hy, sub_self, abs_zero]
      positivity
    · have hstep := prof_step R 0 hR
      simp only [Nat.cast_zero, zero_add, one_mul] at hstep
      unfold swProfile
      rw [hx0, hy]
      exact hstep
  · -- `lnorm x ≥ 1`
    have hmax : (max (lnorm x) 1 : ℕ) = lnorm x := by omega
    rw [hmax]
    rcases lt_trichotomy (lnorm y) (lnorm x) with hlt | heq | hgt
    · -- `lnorm y = lnorm x - 1`
      have hy : lnorm x = lnorm y + 1 := by omega
      have hstep := prof_step R (lnorm y) hR
      unfold swProfile
      rw [hy, abs_sub_comm]
      have hcast : ((lnorm y + 1 : ℕ) : ℝ) = ((lnorm y : ℕ) : ℝ) + 1 := by push_cast; ring
      rw [hcast]
      exact hstep
    · unfold swProfile
      rw [heq]
      simp only [sub_self, abs_zero]
      positivity
    · -- `lnorm y = lnorm x + 1`
      have hy : lnorm y = lnorm x + 1 := by omega
      have hstep := prof_step R (lnorm x) hR
      unfold swProfile
      rw [hy]
      refine hstep.trans ?_
      have hpos : (0:ℝ) < ((lnorm x : ℕ) : ℝ) := by
        have : (1:ℝ) ≤ ((lnorm x : ℕ) : ℝ) := by exact_mod_cast h0
        linarith
      apply div_le_div_of_nonneg_left Real.pi_pos.le (by positivity)
      have : ((lnorm x : ℕ) : ℝ) ≤ ((lnorm x : ℕ) : ℝ) + 1 := by linarith
      exact mul_le_mul_of_nonneg_right this hL.le

/-- Far from the origin the profile is identically zero, so the corresponding
gradient terms vanish. -/
theorem swProfile_far {d R : ℕ} (hR : 1 ≤ R) {x y : Fin d → ℤ} (hxy : adj x y)
    (hx : R < lnorm x) : swProfile d R x - swProfile d R y = 0 := by
  have h2 : lnorm x ≤ lnorm y + 1 := adj_lnorm_le (adj_symm hxy)
  unfold swProfile
  rw [prof_eq_zero hR (by omega), prof_eq_zero hR (by omega), sub_self]

end Phys

import Mathlib

/-!
# Lattice combinatorics and the two-dimensional capacity estimate

In dimension `d ≤ 2` the discrete "capacity" of a point vanishes: there are spin-wave
profiles which equal `π` at the origin, vanish outside a finite box, and have arbitrarily
small Dirichlet energy.  This is the geometric input to the Mermin–Wagner theorem.
-/

open Finset

namespace Phys

/-- The `ℓ^∞` norm on the lattice `ℤ^d`. -/
def lnorm {d : ℕ} (x : Fin d → ℤ) : ℕ := Finset.univ.sup fun i => (x i).natAbs

/-- The box of side `2N+1` centred at the origin. -/
def box (d N : ℕ) : Finset (Fin d → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-(N : ℤ)) (N : ℤ)

/-- Nearest-neighbour adjacency on `ℤ^d`. -/
def adj {d : ℕ} (x y : Fin d → ℤ) : Prop := ∑ i, (x i - y i).natAbs = 1

instance {d : ℕ} : DecidablePred fun p : (Fin d → ℤ) × (Fin d → ℤ) => adj p.1 p.2 :=
  fun _ => by unfold adj; infer_instance

instance {d : ℕ} (x : Fin d → ℤ) : DecidablePred fun y : Fin d → ℤ => adj x y :=
  fun _ => by unfold adj; infer_instance

theorem mem_box {d N : ℕ} {x : Fin d → ℤ} : x ∈ box d N ↔ lnorm x ≤ N := by
  simp only [box, lnorm, Fintype.mem_piFinset, Finset.sup_le_iff, Finset.mem_Icc,
    Finset.mem_univ, forall_const]
  constructor
  · intro h i; have := h i; omega
  · intro h i; have := h i; omega

theorem card_box (d N : ℕ) : (box d N).card = (2 * N + 1) ^ d := by
  rw [box, Fintype.card_piFinset,
    Finset.prod_congr rfl (fun _ _ =>
      show (Finset.Icc (-(N : ℤ)) (N : ℤ)).card = 2 * N + 1 by rw [Int.card_Icc]; omega)]
  simp

theorem box_mono {d : ℕ} {M N : ℕ} (h : M ≤ N) : box d M ⊆ box d N := by
  intro x hx
  rw [mem_box] at hx ⊢
  omega

theorem lnorm_le_of_forall {d : ℕ} {x : Fin d → ℤ} {n : ℕ} (h : ∀ i, (x i).natAbs ≤ n) :
    lnorm x ≤ n := Finset.sup_le fun i _ => h i

theorem le_lnorm {d : ℕ} (x : Fin d → ℤ) (i : Fin d) : (x i).natAbs ≤ lnorm x :=
  Finset.le_sup (f := fun i => (x i).natAbs) (Finset.mem_univ i)

theorem adj_coord_le {d : ℕ} {x y : Fin d → ℤ} (h : adj x y) (i : Fin d) :
    (x i - y i).natAbs ≤ 1 := by
  unfold adj at h
  calc (x i - y i).natAbs ≤ ∑ j, (x j - y j).natAbs :=
        Finset.single_le_sum (f := fun j => (x j - y j).natAbs) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ i)
    _ = 1 := h

theorem adj_lnorm_le {d : ℕ} {x y : Fin d → ℤ} (h : adj x y) : lnorm y ≤ lnorm x + 1 := by
  refine lnorm_le_of_forall fun i => ?_
  have h1 := adj_coord_le h i
  have h2 := le_lnorm x i
  omega

/-- The neighbours of a site inside a box number at most `3 ^ d`. -/
theorem card_nbrs_le {d N : ℕ} (x : Fin d → ℤ) :
    (((box d N).filter fun y => adj x y).card) ≤ 3 ^ d := by
  have hsub : ((box d N).filter fun y => adj x y) ⊆ (box d 1).image fun z => x - z := by
    intro y hy
    rw [Finset.mem_filter] at hy
    refine Finset.mem_image.2 ⟨x - y, ?_, by ring⟩
    rw [mem_box]
    exact lnorm_le_of_forall fun i => adj_coord_le hy.2 i
  calc (((box d N).filter fun y => adj x y).card)
      ≤ ((box d 1).image fun z => x - z).card := Finset.card_le_card hsub
    _ ≤ (box d 1).card := Finset.card_image_le
    _ = 3 ^ d := by rw [card_box]

/-- The number of lattice sites at `ℓ^∞`-distance exactly `k` from the origin. -/
theorem card_shell_le {d N k : ℕ} (hd : d ≤ 2) (hk : 1 ≤ k) :
    (((box d N).filter fun x => lnorm x = k).card) ≤ 8 * k := by
  have hsub : ((box d N).filter fun x => lnorm x = k) ⊆ box d k \ box d (k - 1) := by
    intro x hx
    rw [Finset.mem_filter] at hx
    rw [Finset.mem_sdiff, mem_box, mem_box]
    exact ⟨hx.2.le, by omega⟩
  have hcard : (box d k \ box d (k - 1)).card = (2 * k + 1) ^ d - (2 * (k - 1) + 1) ^ d := by
    rw [Finset.card_sdiff_of_subset (box_mono (by omega)), card_box, card_box]
  have := Finset.card_le_card hsub
  rw [hcard] at this
  refine this.trans ?_
  interval_cases d
  · simp
  · simp; omega
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    have : (2 * (m + 1) + 1) ^ 2 = 4 * m ^ 2 + 12 * m + 9 := by ring
    have h2 : (2 * ((m + 1) - 1) + 1) ^ 2 = 4 * m ^ 2 + 4 * m + 1 := by
      simp only [Nat.add_sub_cancel]; ring
    omega

/-! ### Harmonic sums -/

theorem inv_le_log_diff (i : ℕ) : (1 : ℝ) / (i + 2) ≤ Real.log (i + 2) - Real.log (i + 1) := by
  have h1 : (0:ℝ) < ((i : ℝ) + 1) / ((i : ℝ) + 2) := by positivity
  have h := Real.log_le_sub_one_of_pos h1
  rw [Real.log_div (by positivity) (by positivity)] at h
  have h2 : ((i:ℝ) + 1) / ((i:ℝ) + 2) - 1 = -(1 / ((i:ℝ) + 2)) := by field_simp; ring
  rw [h2] at h
  linarith

theorem harmonic_le (R : ℕ) : ∑ i ∈ Finset.range R, (1 : ℝ) / (i + 1) ≤ 1 + Real.log R := by
  rcases Nat.eq_zero_or_pos R with rfl | hR
  · simp
  obtain ⟨M, rfl⟩ : ∃ M, R = M + 1 := ⟨R - 1, by omega⟩
  rw [Finset.sum_range_succ']
  have hstep : ∑ i ∈ Finset.range M, (1 : ℝ) / ((i : ℝ) + 1 + 1)
      ≤ ∑ i ∈ Finset.range M, (Real.log ((i : ℝ) + 1 + 1) - Real.log ((i : ℝ) + 1)) := by
    refine Finset.sum_le_sum fun i _ => ?_
    have := inv_le_log_diff i
    have e1 : ((i : ℝ) + 1 + 1) = ((i : ℝ) + 2) := by ring
    rw [e1]
    exact this
  have htel : ∑ i ∈ Finset.range M,
      (Real.log (((i : ℝ) + 1) + 1) - Real.log ((i : ℝ) + 1)) = Real.log ((M : ℝ) + 1) := by
    have := Finset.sum_range_sub (fun i : ℕ => Real.log ((i : ℝ) + 1)) M
    simpa using this
  have : ∑ i ∈ Finset.range M, (1 : ℝ) / ((i : ℝ) + 1 + 1) ≤ Real.log ((M : ℝ) + 1) := by
    rw [← htel]; exact hstep
  push_cast
  have h01 : (1 : ℝ) / (0 + 1) = 1 := by norm_num
  rw [h01]
  linarith

/-! ### The spin-wave profile -/

/-- Radial profile of the spin wave: equal to `π` at the origin, vanishing at
`ℓ^∞`-distance `≥ R`, and logarithmically interpolating in between. -/
noncomputable def prof (R k : ℕ) : ℝ :=
  Real.pi * max 0 (1 - Real.log ((k : ℝ) + 1) / Real.log ((R : ℝ) + 1))

/-- The spin-wave profile on the lattice. -/
noncomputable def swProfile (d R : ℕ) (x : Fin d → ℤ) : ℝ := prof R (lnorm x)

theorem prof_zero (R : ℕ) : prof R 0 = Real.pi := by
  simp [prof]

theorem prof_eq_zero {R k : ℕ} (hR : 1 ≤ R) (hk : R ≤ k) : prof R k = 0 := by
  have hL : Real.log ((R : ℝ) + 1) > 0 := by
    apply Real.log_pos; have : (1:ℝ) ≤ (R:ℝ) := by exact_mod_cast hR
    linarith
  have hle : Real.log ((R : ℝ) + 1) ≤ Real.log ((k : ℝ) + 1) := by
    apply Real.log_le_log (by positivity)
    have : (R:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
    linarith
  have : 1 - Real.log ((k : ℝ) + 1) / Real.log ((R : ℝ) + 1) ≤ 0 := by
    rw [sub_nonpos, le_div_iff₀ hL]; linarith
  simp [prof, max_eq_left this]

theorem prof_step (R j : ℕ) (hR : 1 ≤ R) :
    |prof R j - prof R (j + 1)| ≤ Real.pi / (((j : ℝ) + 1) * Real.log ((R : ℝ) + 1)) := by
  have hL0 : Real.log ((R : ℝ) + 1) > 0 := by
    apply Real.log_pos; have : (1:ℝ) ≤ (R:ℝ) := by exact_mod_cast hR
    linarith
  have hcast : (((j + 1 : ℕ) : ℝ) + 1) = (((j : ℝ) + 1) + 1) := by push_cast; ring
  rw [prof, prof, hcast, ← mul_sub, abs_mul, abs_of_pos Real.pi_pos]
  set L := Real.log ((R : ℝ) + 1) with hLdef
  have hL : L > 0 := hL0
  set u : ℝ := 1 - Real.log ((j : ℝ) + 1) / L with hu
  set v : ℝ := 1 - Real.log (((j : ℝ) + 1) + 1) / L with hv
  have hlip : |max 0 u - max 0 v| ≤ |u - v| := by
    rcases abs_cases (max 0 u - max 0 v) with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1] <;>
      rcases le_total u 0 with hu0 | hu0 <;> rcases le_total v 0 with hv0 | hv0 <;>
      simp [max_eq_left, max_eq_right, hu0, hv0] <;>
      rcases abs_cases (u - v) with ⟨h2, _⟩ | ⟨h2, _⟩ <;> rw [h2] <;> linarith
  have huv : u - v = (Real.log (((j : ℝ) + 1) + 1) - Real.log ((j : ℝ) + 1)) / L := by
    rw [hu, hv]; ring
  have hlog : Real.log (((j : ℝ) + 1) + 1) - Real.log ((j : ℝ) + 1) ≤ 1 / ((j : ℝ) + 1) := by
    have h1 : (0:ℝ) < ((j : ℝ) + 2) / ((j : ℝ) + 1) := by positivity
    have h := Real.log_le_sub_one_of_pos h1
    rw [Real.log_div (by positivity) (by positivity)] at h
    have h2 : ((j:ℝ) + 2) / ((j:ℝ) + 1) - 1 = 1 / ((j:ℝ) + 1) := by field_simp; ring
    rw [h2] at h
    have e : ((j : ℝ) + 1 + 1) = ((j : ℝ) + 2) := by ring
    rw [e]; exact h
  have hlognn : 0 ≤ Real.log (((j : ℝ) + 1) + 1) - Real.log ((j : ℝ) + 1) := by
    have : Real.log ((j : ℝ) + 1) ≤ Real.log (((j : ℝ) + 1) + 1) :=
      Real.log_le_log (by positivity) (by linarith)
    linarith
  have habsuv : |u - v| ≤ 1 / (((j : ℝ) + 1) * L) := by
    rw [huv, abs_div, abs_of_pos hL, abs_of_nonneg hlognn, div_le_div_iff₀ hL (by positivity)]
    have hj : (0:ℝ) < (j : ℝ) + 1 := by positivity
    have hmul := mul_le_mul_of_nonneg_right hlog (le_of_lt (mul_pos hj hL))
    have hid : (1 / ((j:ℝ) + 1)) * (((j:ℝ) + 1) * L) = L := by field_simp
    linarith [hmul, hid]
  calc Real.pi * |max 0 u - max 0 v| ≤ Real.pi * (1 / (((j : ℝ) + 1) * L)) := by
        exact mul_le_mul_of_nonneg_left (hlip.trans habsuv) Real.pi_pos.le
    _ = Real.pi / (((j : ℝ) + 1) * L) := by ring

/-! ### The shell sum -/

theorem lnorm_eq_zero {d : ℕ} {x : Fin d → ℤ} (h : lnorm x = 0) : x = 0 := by
  funext i
  have := le_lnorm x i
  rw [h] at this
  have : (x i).natAbs = 0 := by omega
  simpa using this

/-- The key convergent shell sum: in dimension `d ≤ 2` the sum of `1 / max(‖x‖,1)^2`
over a box of size `R` grows only logarithmically. -/
theorem sum_inv_sq_le {d : ℕ} (hd : d ≤ 2) (R : ℕ) :
    ∑ x ∈ box d R, (1 : ℝ) / ((max (lnorm x) 1 : ℕ) : ℝ) ^ 2 ≤ 9 + 8 * Real.log R := by
  classical
  set g : ℕ → ℝ := fun k => (1 : ℝ) / ((max k 1 : ℕ) : ℝ) ^ 2 with hg
  have hgnn : ∀ k, 0 ≤ g k := by intro k; rw [hg]; positivity
  rw [Finset.sum_comp g lnorm]
  have hsub : (box d R).image lnorm ⊆ Finset.range (R + 1) := by
    intro k hk
    rw [Finset.mem_image] at hk
    obtain ⟨x, hx, rfl⟩ := hk
    rw [Finset.mem_range]
    have := mem_box.1 hx
    omega
  have h1 : ∑ k ∈ (box d R).image lnorm, (#{x ∈ box d R | lnorm x = k}) • g k
      ≤ ∑ k ∈ Finset.range (R + 1), (#{x ∈ box d R | lnorm x = k}) • g k := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun k _ _ => ?_
    exact nsmul_nonneg (hgnn k) _
  refine h1.trans ?_
  rw [Finset.sum_range_succ']
  have hzero : (#{x ∈ box d R | lnorm x = 0}) • g 0 ≤ 1 := by
    have hc : (#{x ∈ box d R | lnorm x = 0}) ≤ 1 := by
      refine Finset.card_le_one.2 fun x hx y hy => ?_
      rw [Finset.mem_filter] at hx hy
      rw [lnorm_eq_zero hx.2, lnorm_eq_zero hy.2]
    have hg0 : g 0 = 1 := by norm_num [hg]
    rw [hg0, nsmul_eq_mul, mul_one]
    exact_mod_cast hc
  have hmain : ∀ i ∈ Finset.range R,
      (#{x ∈ box d R | lnorm x = i + 1}) • g (i + 1) ≤ 8 * ((1 : ℝ) / ((i : ℝ) + 1)) := by
    intro i _
    have hc : (#{x ∈ box d R | lnorm x = i + 1}) ≤ 8 * (i + 1) :=
      card_shell_le hd (by omega)
    have hcR : ((#{x ∈ box d R | lnorm x = i + 1} : ℕ) : ℝ) ≤ 8 * ((i : ℝ) + 1) := by
      have := (Nat.cast_le (α := ℝ)).2 hc
      push_cast at this
      linarith
    have hgi : g (i + 1) = 1 / (((i : ℝ) + 1)) ^ 2 := by
      rw [hg]
      simp only [Nat.max_eq_left (Nat.le_add_left 1 i)]
      push_cast
      ring_nf
    rw [nsmul_eq_mul, hgi]
    calc ((#{x ∈ box d R | lnorm x = i + 1} : ℕ) : ℝ) * (1 / ((i : ℝ) + 1) ^ 2)
        ≤ (8 * ((i : ℝ) + 1)) * (1 / ((i : ℝ) + 1) ^ 2) := by
          exact mul_le_mul_of_nonneg_right hcR (by positivity)
      _ = 8 * (1 / ((i : ℝ) + 1)) := by field_simp
  have hsum := Finset.sum_le_sum hmain
  have hharm := harmonic_le R
  have hrw : ∑ i ∈ Finset.range R, 8 * ((1 : ℝ) / ((i : ℝ) + 1))
      = 8 * ∑ i ∈ Finset.range R, (1 : ℝ) / ((i : ℝ) + 1) := by
    rw [Finset.mul_sum]
  rw [hrw] at hsum
  linarith

end Phys

