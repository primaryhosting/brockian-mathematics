/-
# Penrose Singularity
Category: Frontier Physics
Target: Frontier.penrose_singularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Penrose Singularity
Category: Frontier Physics
Target: Frontier.penrose_singularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ENNReal

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-!
## The focusing mechanism behind the Penrose singularity theorem

The physical content of the Penrose singularity theorem is the *focusing* of a null geodesic
congruence.  Along a null geodesic congruence with vanishing twist (such as the family of null
geodesics orthogonal to a closed codimension-two surface), the expansion `θ` of the congruence,
as a function of the affine parameter `t`, obeys the Raychaudhuri equation

  `θ' = - θ² / 2 - σ_{ab} σ^{ab} - Ric(k, k)`

in four spacetime dimensions.  The shear term `σ_{ab} σ^{ab}` is nonnegative, and the null energy
condition gives `Ric(k, k) ≥ 0` (via the Einstein equations, `Ric(k,k) = 8π T(k,k) ≥ 0` for a null
vector `k`).  Hence the *Raychaudhuri inequality*

  `θ' ≤ - θ² / 2`

holds along every generator.  A *trapped surface* is by definition a closed codimension-two
surface whose two null normal congruences both have strictly negative initial expansion,
`θ 0 < 0`.

The content formalized below is the resulting incompleteness: an affinely parametrized generator
of such a congruence cannot be extended to arbitrarily large affine parameter; in fact its affine
length is at most `-2 / θ 0`.  This is the analytic heart of the Penrose theorem (the remaining
ingredients of Penrose's argument are the global causal-theoretic ones, which turn the finiteness
of the affine length into the statement that the boundary of the future of the trapped surface is
compact and hence that the spacetime cannot be null geodesically complete).
-/

/-- The analytic datum attached to a generator of a null geodesic congruence with vanishing
twist: its expansion `theta`, as a function of the affine parameter, together with a derivative
`theta'`, defined for affine parameter in `[0, length)`, where `length ∈ ℝ≥0∞` is the affine
length of the maximal extension of the generator (so `length = ⊤` means the generator is future
affinely complete). The field `raychaudhuri` records the Raychaudhuri inequality
`θ' ≤ -θ²/2`, which holds for a twist-free null congruence in a spacetime satisfying the null
energy condition. -/
structure NullCongruence where
  /-- Affine length of the maximal future extension of the generator. -/
  length : ℝ≥0∞
  /-- The expansion of the congruence as a function of the affine parameter. -/
  theta : ℝ → ℝ
  /-- The derivative of the expansion. -/
  theta' : ℝ → ℝ
  /-- `theta'` really is the derivative of `theta` along the generator. -/
  hasDeriv : ∀ t : ℝ, 0 ≤ t → ENNReal.ofReal t < length → HasDerivAt theta (theta' t) t
  /-- Raychaudhuri's equation together with the null energy condition (`Ric(k,k) ≥ 0`) and the
  nonnegativity of the shear squared. -/
  raychaudhuri : ∀ t : ℝ, 0 ≤ t → ENNReal.ofReal t < length → theta' t ≤ -(theta t) ^ 2 / 2

namespace NullCongruence

variable (C : NullCongruence)

/-- The generator emanates from a *trapped* surface: the initial expansion is negative. -/
def Trapped : Prop := C.theta 0 < 0

/-- The generator is future affinely complete, i.e. its affine parameter ranges over all
of `[0, ∞)`. -/
def Complete : Prop := C.length = ⊤

end NullCongruence

/-! ### The core analytic lemma -/

/-- Along a stretch `[0, b]` of affine parameter on which the Raychaudhuri inequality
`θ' ≤ -θ²/2` holds, the expansion is nonincreasing; in particular it never exceeds its
initial value. -/
lemma theta_antitone_of_raychaudhuri {theta theta' : ℝ → ℝ} {b : ℝ} (hb : 0 ≤ b)
    (hd : ∀ t ∈ Set.Icc (0 : ℝ) b, HasDerivAt theta (theta' t) t)
    (hr : ∀ t ∈ Set.Icc (0 : ℝ) b, theta' t ≤ -(theta t) ^ 2 / 2) :
    ∀ t ∈ Set.Icc (0 : ℝ) b, theta t ≤ theta 0 := by
  have hanti : AntitoneOn theta (Set.Icc (0 : ℝ) b) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc _ _) ?_ ?_ ?_
    · exact fun t ht => ((hd t ht).continuousAt).continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      exact ((hd t (Set.mem_Icc_of_Ioo ht)).differentiableAt).differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have hmem : t ∈ Set.Icc (0 : ℝ) b := Set.mem_Icc_of_Ioo ht
      have : deriv theta t = theta' t := (hd t hmem).deriv
      rw [this]
      have := hr t hmem
      nlinarith [sq_nonneg (theta t)]
  intro t ht
  exact hanti (Set.left_mem_Icc.mpr hb) ht ht.1

/-- **Focusing.** If the Raychaudhuri inequality `θ' ≤ -θ²/2` holds on the affine-parameter
interval `[0, b]` and the initial expansion `θ 0` is negative (trapped surface), then
`b < -2 / θ 0`: the congruence focuses to a caustic within affine parameter `-2 / θ 0`. -/
theorem focusing_bound {theta theta' : ℝ → ℝ} {b : ℝ} (hb : 0 ≤ b)
    (hd : ∀ t ∈ Set.Icc (0 : ℝ) b, HasDerivAt theta (theta' t) t)
    (hr : ∀ t ∈ Set.Icc (0 : ℝ) b, theta' t ≤ -(theta t) ^ 2 / 2)
    (h0 : theta 0 < 0) : b < -2 / theta 0 := by
  have hle := theta_antitone_of_raychaudhuri hb hd hr
  have hneg : ∀ t ∈ Set.Icc (0 : ℝ) b, theta t < 0 := fun t ht => lt_of_le_of_lt (hle t ht) h0
  -- `u t = 1 / θ t - t / 2` is monotone on `[0, b]`.
  set u : ℝ → ℝ := fun t => 1 / theta t - t / 2 with hu
  have hud : ∀ t ∈ Set.Icc (0 : ℝ) b,
      HasDerivAt u (-theta' t / (theta t) ^ 2 - 1 / 2) t := by
    intro t ht
    have hne : theta t ≠ 0 := ne_of_lt (hneg t ht)
    have h1 : HasDerivAt (fun s => 1 / theta s) (-theta' t / (theta t) ^ 2) t := by
      have := (hd t ht).inv hne
      simpa [one_div, div_eq_mul_inv, neg_div] using this
    have h2 : HasDerivAt (fun s : ℝ => s / 2) (1 / 2) t := by
      simpa using (hasDerivAt_id t).div_const 2
    simpa [hu] using h1.sub h2
  have hmono : MonotoneOn u (Set.Icc (0 : ℝ) b) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) ?_ ?_ ?_
    · exact fun t ht => ((hud t ht).continuousAt).continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      exact ((hud t (Set.mem_Icc_of_Ioo ht)).differentiableAt).differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have hmem : t ∈ Set.Icc (0 : ℝ) b := Set.mem_Icc_of_Ioo ht
      rw [(hud t hmem).deriv]
      have hlt := hneg t hmem
      have hsq : 0 < (theta t) ^ 2 := by nlinarith
      have hrt := hr t hmem
      have hkey : 1 / 2 ≤ -theta' t / (theta t) ^ 2 := by
        rw [le_div_iff₀ hsq]
        nlinarith
      linarith
  have hb0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) b := Set.left_mem_Icc.mpr hb
  have hbb : b ∈ Set.Icc (0 : ℝ) b := Set.right_mem_Icc.mpr hb
  have := hmono hb0 hbb hb
  simp only [hu] at this
  have hbneg : theta b < 0 := hneg b hbb
  have h1 : 1 / theta b < 0 := div_neg_of_pos_of_neg one_pos hbneg
  have h2 : 1 / theta 0 - 0 / 2 ≤ 1 / theta b - b / 2 := this
  have heq : (-2 : ℝ) / theta 0 = -(1 / theta 0) * 2 := by field_simp
  rw [heq]
  linarith

/-! ### The Penrose singularity theorem (focusing form) -/

/-- **Penrose singularity theorem** (analytic core).  A generator of a twist-free null geodesic
congruence issuing from a trapped surface (`θ 0 < 0`) in a spacetime satisfying the null energy
condition (so that the Raychaudhuri inequality `θ' ≤ -θ²/2` holds) is *not* future affinely
complete: its affine length is at most `-2 / θ 0`, hence finite.  In particular the spacetime is
null geodesically incomplete. -/
theorem penrose_singularity (C : NullCongruence) (h : C.Trapped) :
    C.length ≤ ENNReal.ofReal (-2 / C.theta 0) ∧ ¬ C.Complete := by
  have h0 : C.theta 0 < 0 := h
  have hpos : 0 < -2 / C.theta 0 := div_pos_of_neg_of_neg (by norm_num) h0
  have hmain : C.length ≤ ENNReal.ofReal (-2 / C.theta 0) := by
    by_contra hcon
    push_neg at hcon
    set b : ℝ := -2 / C.theta 0 with hbdef
    have hb : 0 ≤ b := le_of_lt hpos
    have hblt : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) b → ENNReal.ofReal t < C.length := by
      intro t ht
      have hle : ENNReal.ofReal t ≤ ENNReal.ofReal b := ENNReal.ofReal_le_ofReal ht.2
      exact lt_of_le_of_lt hle hcon
    have hd : ∀ t ∈ Set.Icc (0 : ℝ) b, HasDerivAt C.theta (C.theta' t) t :=
      fun t ht => C.hasDeriv t ht.1 (hblt t ht)
    have hr : ∀ t ∈ Set.Icc (0 : ℝ) b, C.theta' t ≤ -(C.theta t) ^ 2 / 2 :=
      fun t ht => C.raychaudhuri t ht.1 (hblt t ht)
    have := focusing_bound hb hd hr h0
    exact absurd this (lt_irrefl b)
  refine ⟨hmain, ?_⟩
  intro hc
  rw [NullCongruence.Complete] at hc
  rw [hc] at hmain
  simp at hmain

/-! ### Sharpness and non-vacuity

The hypotheses of `Frontier.penrose_singularity` are satisfiable, and the bound on the affine
length that it provides is sharp: the exact solution `θ t = 2 / (t - 1)` of the Raychaudhuri
equation `θ' = -θ²/2` (zero shear, zero null Ricci curvature) has `θ 0 = -2 < 0` and blows up
exactly at affine parameter `1 = -2 / θ 0`. -/

/-- A generator realizing the extremal case of the focusing bound: the exact Raychaudhuri
solution `θ t = 2 / (t - 1)`, defined for affine parameter in `[0, 1)`. -/
noncomputable def sharpCongruence : NullCongruence where
  length := 1
  theta := fun t => 2 / (t - 1)
  theta' := fun t => -2 / (t - 1) ^ 2
  hasDeriv := by
    intro t _ ht
    have ht1 : t < 1 := ENNReal.ofReal_lt_one.mp ht
    have h1 : HasDerivAt (fun s : ℝ => s - 1) 1 t := (hasDerivAt_id t).sub_const 1
    have hne : t - 1 ≠ 0 := by intro h; linarith [sub_eq_zero.mp h]
    have h2 := (h1.inv hne).const_mul (2 : ℝ)
    have hfun : (fun y : ℝ => 2 * ((fun s : ℝ => s - 1)⁻¹ y)) = fun s : ℝ => 2 / (s - 1) := by
      funext s; simp [div_eq_mul_inv]
    rw [hfun] at h2
    convert h2 using 1
    ring
  raychaudhuri := by
    intro t _ ht
    have ht1 : t < 1 := ENNReal.ofReal_lt_one.mp ht
    have hne : t - 1 ≠ 0 := by intro h; linarith [sub_eq_zero.mp h]
    have hpos : 0 < (t - 1) ^ 2 := by positivity
    have heq : -(2 / (t - 1)) ^ 2 / 2 = -2 / (t - 1) ^ 2 := by
      field_simp
    rw [heq]

/-- The extremal generator does issue from a trapped surface. -/
lemma sharpCongruence_trapped : sharpCongruence.Trapped := by
  show (2 : ℝ) / ((0 : ℝ) - 1) < 0
  norm_num

/-- Sharpness of the Penrose focusing bound: for the extremal generator the affine length is
exactly `-2 / θ 0`. -/
lemma sharpCongruence_length :
    sharpCongruence.length = ENNReal.ofReal (-2 / sharpCongruence.theta 0) := by
  show (1 : ℝ≥0∞) = ENNReal.ofReal (-2 / ((2 : ℝ) / ((0 : ℝ) - 1)))
  norm_num

end Frontier

