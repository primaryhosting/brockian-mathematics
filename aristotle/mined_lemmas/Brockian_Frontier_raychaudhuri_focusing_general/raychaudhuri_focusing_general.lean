import Mathlib

/-!
# Brockian packaging of the Hawking focusing / singularity argument

This file contains

* `Brockian.Frontier.raychaudhuri_focusing_general`: the analytic core.  If a real function
  `theta` ("expansion") satisfies a Raychaudhuri-type differential inequality
  `theta' ≤ -theta ^ 2 / n` on `[0, L)` and starts negative, then `L ≤ -n / theta 0`.
  The constant `n` is the number of transverse dimensions: `n = 3` for a timelike
  congruence in `3 + 1` dimensions (Hawking), `n = 2` for a null congruence (Penrose).

* `Brockian.Frontier.TimelikeCongruence` and `Brockian.Frontier.hawking_focusing`: the
  timelike (`n = 3`) packaging requested, and its proof.

* `Brockian.Frontier.NullCongruence` and `Brockian.Frontier.penrose_focusing`: the null
  (`n = 2`) specialisation, for comparison.

* `Brockian.Frontier.ExpandingCauchy`, `Brockian.Frontier.TimelikeGeodesicallyComplete`
  and `Brockian.Frontier.hawking_singularity`: a geometric packaging of the cosmological
  setting.  Since Mathlib has no Lorentzian geometry, the packaging is *abstract*: the
  data of a Cauchy surface with a uniformly expanding orthogonal geodesic congruence is
  recorded as the family of expansion scalars along the generators together with the
  Raychaudhuri inequality (which encodes the strong energy condition and vanishing
  vorticity) and the uniform expansion bound `theta i 0 ≤ -c < 0`.  Timelike geodesic
  completeness is taken in the form it is actually used in Hawking's argument: every
  generator can be continued, with a smooth expansion scalar, to arbitrarily large proper
  time.  The theorem says this is impossible.
-/

namespace Brockian.Frontier

open Set

/-! ### The analytic focusing lemma -/

/-- **Raychaudhuri focusing, general transverse dimension.**

If `theta : ℝ → ℝ` has derivative `dtheta` on `[0, L)`, satisfies the Raychaudhuri
inequality `dtheta τ ≤ -(theta τ) ^ 2 / n` there (`n > 0`), and is negative at `τ = 0`,
then the interval on which this is possible has length at most `-n / theta 0`.

Proof: `theta` is antitone, hence stays `≤ theta 0 < 0`; therefore `1 / theta` is
differentiable with derivative `-dtheta / theta ^ 2 ≥ 1 / n`, so
`1 / theta τ ≥ 1 / theta 0 + τ / n`, while `1 / theta τ < 0`. -/

theorem raychaudhuri_focusing_general {L n : ℝ} {theta dtheta : ℝ → ℝ} (hn : 0 < n)
    (hderiv : ∀ τ ∈ Ico (0 : ℝ) L, HasDerivAt theta (dtheta τ) τ)
    (hRay : ∀ τ ∈ Ico (0 : ℝ) L, dtheta τ ≤ -(theta τ) ^ 2 / n)
    (h0 : theta 0 < 0) :
    L ≤ -n / theta 0 := by
  have hbound : 0 < -n / theta 0 := div_pos_of_neg_of_neg (by linarith) h0
  -- `theta` is antitone on `[0, L)`
  have hcont : ContinuousOn theta (Ico 0 L) := fun x hx =>
    (hderiv x hx).continuousAt.continuousWithinAt
  have hsub : Ioo (0 : ℝ) L ⊆ Ico (0 : ℝ) L := Ioo_subset_Ico_self
  have hanti : AntitoneOn theta (Ico 0 L) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ico 0 L) hcont ?_ ?_
    · intro x hx
      rw [interior_Ico] at hx
      exact (hderiv x (hsub hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ico] at hx
      rw [(hderiv x (hsub hx)).deriv]
      have hR := hRay x (hsub hx)
      have h2 : 0 ≤ (theta x) ^ 2 / n := div_nonneg (sq_nonneg _) hn.le
      rw [neg_div] at hR
      linarith
  have hmem0 : ∀ τ ∈ Ico (0 : ℝ) L, (0 : ℝ) ∈ Ico (0 : ℝ) L := fun τ hτ =>
    ⟨le_refl 0, lt_of_le_of_lt hτ.1 hτ.2⟩
  have hneg : ∀ τ ∈ Ico (0 : ℝ) L, theta τ ≤ theta 0 := fun τ hτ =>
    hanti (hmem0 τ hτ) hτ hτ.1
  -- the reciprocal, corrected by `τ / n`, is monotone
  set w : ℝ → ℝ := fun τ => (theta τ)⁻¹ - τ / n with hw
  have hwderiv : ∀ x ∈ Ioo (0 : ℝ) L,
      HasDerivAt w (-dtheta x / (theta x) ^ 2 - 1 / n) x := by
    intro x hx
    have hx' := hsub hx
    have hne : theta x ≠ 0 := ne_of_lt (lt_of_le_of_lt (hneg x hx') h0)
    exact ((hderiv x hx').inv hne).sub ((hasDerivAt_id x).div_const n)
  have hwcont : ContinuousOn w (Ico 0 L) := by
    intro x hx
    have hne : theta x ≠ 0 := ne_of_lt (lt_of_le_of_lt (hneg x hx) h0)
    exact HasDerivAt.continuousAt
      (((hderiv x hx).inv hne).sub ((hasDerivAt_id x).div_const n)) |>.continuousWithinAt
  have hwmono : MonotoneOn w (Ico 0 L) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ico 0 L) hwcont ?_ ?_
    · intro x hx
      rw [interior_Ico] at hx
      exact (hwderiv x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ico] at hx
      rw [(hwderiv x hx).deriv]
      have hx' := hsub hx
      have hlt : theta x < 0 := lt_of_le_of_lt (hneg x hx') h0
      have hsq : 0 < (theta x) ^ 2 := by nlinarith
      have hR := hRay x hx'
      rw [neg_div] at hR
      rw [sub_nonneg, le_div_iff₀ hsq]
      have hmul : (1 : ℝ) / n * (theta x) ^ 2 = (theta x) ^ 2 / n := by ring
      rw [hmul]
      linarith
  -- conclude
  have key : ∀ τ ∈ Ico (0 : ℝ) L, τ < -n / theta 0 := by
    intro τ hτ
    have hmono := hwmono (hmem0 τ hτ) hτ hτ.1
    have hlt : theta τ < 0 := lt_of_le_of_lt (hneg τ hτ) h0
    have hinvneg : (theta τ)⁻¹ < 0 := inv_lt_zero'.2 hlt
    have hinv0 : (theta 0)⁻¹ < 0 := inv_lt_zero'.2 h0
    simp only [hw, zero_div, sub_zero] at hmono
    have hτn : τ / n < -(theta 0)⁻¹ := by linarith
    have : τ < -(theta 0)⁻¹ * n := by
      rw [div_lt_iff₀ hn] at hτn; linarith
    calc τ < -(theta 0)⁻¹ * n := this
      _ = -n / theta 0 := by field_simp
  by_contra hcon
  push_neg at hcon
  exact absurd (key (-n / theta 0) ⟨le_of_lt hbound, hcon⟩) (lt_irrefl _)

/-- Shifted form of the focusing lemma, the step needed for the Hawking–Penrose
unification: a congruence obeying the Raychaudhuri inequality on all of `[0, ∞)` cannot
have negative expansion at *any* time.  (In Hawking–Penrose the genericity condition is
what forces the expansion to become negative somewhere along each complete causal
geodesic; this lemma turns that into a contradiction.) -/
