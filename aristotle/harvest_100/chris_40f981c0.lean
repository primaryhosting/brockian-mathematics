import Mathlib

/-!
# Brouwer 2 D
Category: Pure Mathematics
Target: Math.brouwer_2d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real
open Metric Set

namespace Brouwer2D

noncomputable section

/-- The punctured complex plane, the base of the exponential covering map. -/
abbrev Cstar := {z : ℂ // z ≠ 0}

/-- The exponential covering map `ℂ → ℂ \ {0}`. -/
def pexp (z : ℂ) : Cstar := ⟨Complex.exp z, Complex.exp_ne_zero z⟩

theorem isCoveringMap_pexp : IsCoveringMap pexp := Complex.isCoveringMap_exp

/-- A continuous map into `ℂ` whose exponential is constantly `1`, defined on a preconnected
space, is constant. -/
theorem const_of_exp_eq_one {A : Type*} [TopologicalSpace A] [PreconnectedSpace A] {g : A → ℂ}
    (hg : Continuous g) (h : ∀ x, Complex.exp (g x) = 1) (x y : A) : g x = g y :=
  isCoveringMap_pexp.isSeparatedMap.const_of_comp
    isCoveringMap_pexp.isLocalHomeomorph.isLocallyInjective hg
    (fun a a' => Subtype.ext (by simp [pexp, h])) x y

/-- The standard parametrization of the unit circle. -/
def ee (t : ℝ) : ℂ := Complex.exp ((2 * Real.pi * t : ℝ) * Complex.I)

theorem continuous_ee : Continuous ee := by
  unfold ee
  fun_prop

theorem norm_ee (t : ℝ) : ‖ee t‖ = 1 := by
  rw [ee, Complex.norm_exp_ofReal_mul_I]

theorem ee_zero : ee 0 = 1 := by
  simp [ee]

theorem ee_one : ee 1 = 1 := by
  have : ((2 * Real.pi * 1 : ℝ) : ℂ) * Complex.I = 2 * Real.pi * Complex.I := by
    push_cast; ring
  rw [ee, this, Complex.exp_two_pi_mul_I]

/-- Clamped parameter controlling the radius. -/
def aa (s : ℝ) : ℝ := min (max (2 * s) 0) 1

/-- Clamped parameter controlling the amount of `f` subtracted. -/
def bb (s : ℝ) : ℝ := min (max (2 - 2 * s) 0) 1

theorem continuous_aa : Continuous aa := by unfold aa; fun_prop

theorem continuous_bb : Continuous bb := by unfold bb; fun_prop

theorem aa_nonneg (s : ℝ) : 0 ≤ aa s := le_min (le_max_right _ _) zero_le_one

theorem aa_le_one (s : ℝ) : aa s ≤ 1 := min_le_right _ _

theorem bb_nonneg (s : ℝ) : 0 ≤ bb s := le_min (le_max_right _ _) zero_le_one

theorem bb_le_one (s : ℝ) : bb s ≤ 1 := min_le_right _ _

theorem aa_zero : aa 0 = 0 := by norm_num [aa]

theorem bb_zero : bb 0 = 1 := by norm_num [bb]

theorem aa_one : aa 1 = 1 := by norm_num [aa]

theorem bb_one : bb 1 = 0 := by norm_num [bb]

theorem aa_eq_one_or_bb_eq_one (s : ℝ) : aa s = 1 ∨ bb s = 1 := by
  rcases le_or_gt s (1 / 2) with h | h
  · right
    have : (1 : ℝ) ≤ 2 - 2 * s := by linarith
    have h0 : (0 : ℝ) ≤ 2 - 2 * s := by linarith
    rw [bb, max_eq_left h0, min_eq_right this]
  · left
    have h1 : (1 : ℝ) ≤ 2 * s := by linarith
    have h0 : (0 : ℝ) ≤ 2 * s := by linarith
    rw [aa, max_eq_left h0, min_eq_right h1]

section Main

variable {f : ℂ → ℂ}

/-- The homotopy, as a map `ℝ × ℝ → ℂ`: it interpolates from the constant loop `-f 0`
(at `s = 0`) through the loop `z - f z` on the unit circle (at `s = 1/2`) to the loop
`z` (at `s = 1`). -/
def ww (f : ℂ → ℂ) (s t : ℝ) : ℂ :=
  (aa s : ℂ) * ee t - (bb s : ℂ) * f ((aa s : ℂ) * ee t)

theorem norm_arg_le_one (s t : ℝ) : ‖(aa s : ℂ) * ee t‖ ≤ 1 := by
  rw [norm_mul, norm_ee, Complex.norm_real, Real.norm_eq_abs, mul_one,
    abs_of_nonneg (aa_nonneg s)]
  exact aa_le_one s

theorem arg_mem_ball (s t : ℝ) : (aa s : ℂ) * ee t ∈ closedBall (0 : ℂ) 1 := by
  simpa [mem_closedBall, dist_eq_norm] using norm_arg_le_one s t

theorem continuous_ww (hf : ContinuousOn f (closedBall (0 : ℂ) 1)) :
    Continuous fun p : ℝ × ℝ => ww f p.1 p.2 := by
  have hz : Continuous fun p : ℝ × ℝ => (aa p.1 : ℂ) * ee p.2 := by
    have h1 : Continuous fun p : ℝ × ℝ => ((aa p.1 : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp (continuous_aa.comp continuous_fst)
    exact h1.mul (continuous_ee.comp continuous_snd)
  have hfc : Continuous fun p : ℝ × ℝ => f ((aa p.1 : ℂ) * ee p.2) :=
    hf.comp_continuous hz fun p => arg_mem_ball p.1 p.2
  have hb : Continuous fun p : ℝ × ℝ => ((bb p.1 : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_bb.comp continuous_fst)
  exact hz.sub (hb.mul hfc)

theorem ww_ne_zero (hmaps : MapsTo f (closedBall (0 : ℂ) 1) (closedBall (0 : ℂ) 1))
    (hfix : ∀ z ∈ closedBall (0 : ℂ) 1, f z ≠ z) (s t : ℝ) :
    ww f s t ≠ 0 := by
  rcases eq_or_lt_of_le (bb_le_one s) with hb | hb
  · -- `bb s = 1`: the value is `z - f z` with `z` in the disk
    rw [ww, hb]
    intro hcon
    have : f ((aa s : ℂ) * ee t) = (aa s : ℂ) * ee t := by
      have := sub_eq_zero.mp (by simpa using hcon)
      linear_combination -this
    exact hfix _ (arg_mem_ball s t) this
  · -- `bb s < 1`, hence `aa s = 1`
    have ha : aa s = 1 := by
      rcases aa_eq_one_or_bb_eq_one s with h | h
      · exact h
      · exact absurd h (ne_of_lt hb)
    have hnf : ‖f ((aa s : ℂ) * ee t)‖ ≤ 1 := by
      have := hmaps (arg_mem_ball s t)
      simpa [mem_closedBall, dist_eq_norm] using this
    intro hcon
    have h0 : (aa s : ℂ) * ee t = (bb s : ℂ) * f ((aa s : ℂ) * ee t) := by
      have := sub_eq_zero.mp hcon
      exact this
    have h1 : ‖(aa s : ℂ) * ee t‖ = 1 := by
      rw [norm_mul, norm_ee, Complex.norm_real, Real.norm_eq_abs, mul_one, ha, abs_one]
    have h2 : ‖(bb s : ℂ) * f ((aa s : ℂ) * ee t)‖ ≤ bb s := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (bb_nonneg s)]
      nlinarith [bb_nonneg s, norm_nonneg (f ((aa s : ℂ) * ee t))]
    rw [h0] at h1
    linarith [h1 ▸ h2]

theorem ww_one (s : ℝ) : ww f s 1 = ww f s 0 := by
  rw [ww, ww, ee_one, ee_zero]

theorem ww_at_one (t : ℝ) : ww f 1 t = ee t := by
  rw [ww, aa_one, bb_one]
  push_cast
  ring

theorem ww_at_zero (t : ℝ) : ww f 0 t = -f 0 := by
  rw [ww, aa_zero, bb_zero]
  push_cast
  simp

end Main

/-- **Brouwer's fixed point theorem** in dimension 2, complex formulation. -/
theorem brouwer_disk_complex {f : ℂ → ℂ} (hf : ContinuousOn f (closedBall (0 : ℂ) 1))
    (hmaps : MapsTo f (closedBall (0 : ℂ) 1) (closedBall (0 : ℂ) 1)) :
    ∃ z ∈ closedBall (0 : ℂ) 1, f z = z := by
  by_contra hcon
  push_neg at hcon
  have hfix : ∀ z ∈ closedBall (0 : ℂ) 1, f z ≠ z := hcon
  -- the homotopy as a continuous map into the punctured plane
  have hne : ∀ s t : unitInterval, ww f (s : ℝ) (t : ℝ) ≠ 0 := fun s t =>
    ww_ne_zero hmaps hfix _ _
  set W : C(unitInterval × unitInterval, Cstar) :=
    ⟨fun p => ⟨ww f (p.1 : ℝ) (p.2 : ℝ), hne p.1 p.2⟩, by
      apply Continuous.subtype_mk
      exact (continuous_ww hf).comp
        ((continuous_subtype_val.comp continuous_fst).prodMk
          (continuous_subtype_val.comp continuous_snd))⟩ with hW
  -- the base point of the lift
  have hf0 : -f 0 ≠ 0 := by
    have h0 : (0 : ℂ) ∈ closedBall (0 : ℂ) 1 := by simp
    simpa using fun h => hfix 0 h0 (by simpa using h)
  set c : ℂ := Complex.log (-f 0)
  have hexpc : Complex.exp c = -f 0 := Complex.exp_log hf0
  have H0 : ∀ t : unitInterval, W (0, t) = pexp c := by
    intro t
    apply Subtype.ext
    simp only [hW, ContinuousMap.coe_mk, pexp, hexpc]
    simpa using ww_at_zero (f := f) (t : ℝ)
  set L : C(unitInterval × unitInterval, ℂ) :=
    isCoveringMap_pexp.liftHomotopy W (ContinuousMap.const _ c) H0
  have hlifts : ∀ p : unitInterval × unitInterval, Complex.exp (L p) = ww f (p.1 : ℝ) (p.2 : ℝ) := by
    intro p
    have := congr_fun (isCoveringMap_pexp.liftHomotopy_lifts W (ContinuousMap.const _ c) H0) p
    have := congrArg Subtype.val this
    simpa [pexp, hW] using this
  have hL0 : ∀ t : unitInterval, L (0, t) = c :=
    fun t => isCoveringMap_pexp.liftHomotopy_zero W (ContinuousMap.const _ c) H0 t
  -- the two vertical boundary edges of the lifted square agree
  have hend : L (1, 1) = L (1, 0) := by
    have hcont : Continuous fun s : unitInterval => L (s, 1) - L (s, 0) := by
      exact (L.continuous.comp (continuous_id.prodMk continuous_const)).sub
        (L.continuous.comp (continuous_id.prodMk continuous_const))
    have hexp : ∀ s : unitInterval, Complex.exp (L (s, 1) - L (s, 0)) = 1 := by
      intro s
      rw [Complex.exp_sub, hlifts (s, 1), hlifts (s, 0)]
      have h1 : ((1 : unitInterval) : ℝ) = 1 := rfl
      have h0 : ((0 : unitInterval) : ℝ) = 0 := rfl
      rw [h1, h0, ww_one (f := f) (s : ℝ)]
      exact div_self (ww_ne_zero hmaps hfix (s : ℝ) 0)
    have := const_of_exp_eq_one hcont hexp 1 0
    simp only [hL0] at this
    exact sub_eq_zero.mp (by simpa using this)
  -- but the top edge of the lift is a lift of the loop `t ↦ ee t`, which winds once
  have hwind : L (1, 1) = L (1, 0) + 2 * Real.pi * Complex.I := by
    have hcont : Continuous fun t : unitInterval =>
        L (1, t) - (2 * Real.pi * Complex.I) * (t : ℝ) := by
      refine (L.continuous.comp (continuous_const.prodMk continuous_id)).sub ?_
      exact continuous_const.mul (Complex.continuous_ofReal.comp continuous_subtype_val)
    have hexp : ∀ t : unitInterval,
        Complex.exp (L (1, t) - (2 * Real.pi * Complex.I) * (t : ℝ)) = 1 := by
      intro t
      rw [Complex.exp_sub, hlifts (1, t)]
      have h1 : ((1 : unitInterval) : ℝ) = 1 := rfl
      rw [h1, ww_at_one]
      have : Complex.exp ((2 * Real.pi * Complex.I) * (t : ℝ)) = ee (t : ℝ) := by
        rw [ee]
        congr 1
        push_cast
        ring
      rw [this]
      exact div_self (by simp [ee, Complex.exp_ne_zero])
    have := const_of_exp_eq_one hcont hexp 1 0
    have h1 : ((1 : unitInterval) : ℝ) = 1 := rfl
    have h0 : ((0 : unitInterval) : ℝ) = 0 := rfl
    rw [h1, h0] at this
    push_cast at this
    linear_combination this
  rw [hend] at hwind
  have : (2 : ℂ) * Real.pi * Complex.I = 0 := by linear_combination -hwind
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  simp [Complex.I_ne_zero, hpi] at this

end

end Brouwer2D

namespace Math

/-- **Brouwer's fixed point theorem in dimension 2**: every continuous self-map of the closed
unit 2-disk has a fixed point. -/
theorem brouwer_2d (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (hf : ContinuousOn f (closedBall 0 1))
    (hmaps : MapsTo f (closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) (closedBall 0 1)) :
    ∃ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, f x = x := by
  -- transfer the statement to `ℂ` along a linear isometry `ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2)`
  set e := Complex.orthonormalBasisOneI.repr
  have hmem : ∀ z : ℂ, z ∈ closedBall (0 : ℂ) 1 →
      e z ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
    intro z hz
    simp only [mem_closedBall, dist_zero_right, e.norm_map] at *
    exact hz
  have hmem' : ∀ x : EuclideanSpace ℝ (Fin 2), x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 →
      e.symm x ∈ closedBall (0 : ℂ) 1 := by
    intro x hx
    simp only [mem_closedBall, dist_zero_right, e.symm.norm_map] at *
    exact hx
  have hcont : ContinuousOn (fun w : ℂ => e.symm (f (e w))) (closedBall (0 : ℂ) 1) := by
    refine e.symm.continuous.comp_continuousOn (hf.comp e.continuous.continuousOn ?_)
    exact fun z hz => hmem z hz
  have hmaps' : MapsTo (fun w : ℂ => e.symm (f (e w))) (closedBall (0 : ℂ) 1)
      (closedBall (0 : ℂ) 1) := fun z hz => hmem' _ (hmaps (hmem z hz))
  obtain ⟨z, hz, hzfix⟩ := Brouwer2D.brouwer_disk_complex hcont hmaps'
  refine ⟨e z, hmem z hz, ?_⟩
  have := congrArg e hzfix
  simpa using this

end Math

