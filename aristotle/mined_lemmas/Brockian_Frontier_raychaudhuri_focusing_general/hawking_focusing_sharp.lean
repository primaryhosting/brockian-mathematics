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

theorem hawking_focusing_sharp :
    ∃ C : TimelikeCongruence 1, (1 : ℝ) = -3 / C.theta 0 := by
  refine ⟨{ theta := fun τ => 3 / (τ - 1)
            dtheta := fun τ => -3 / (τ - 1) ^ 2
            hderiv := ?_
            hRay := ?_
            htrapped := by norm_num }, by norm_num⟩
  · intro x hx
    have hne : x - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_lt hx.2)
    have h := (hasDerivAt_id x).sub_const 1
    have h2 := (hasDerivAt_const x (3 : ℝ)).div h hne
    simp only [id] at h2
    convert h2 using 1
    ring
  · intro x hx
    have hne : x - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_lt hx.2)
    have heq : -(3 / (x - 1)) ^ 2 / 3 = -3 / (x - 1) ^ 2 := by field_simp
    rw [heq]

/-! ### The null (Penrose) specialisation, for comparison -/

/-- Null expansion of a vorticity-free congruence on an affine interval `[0, L)`:
the same data with the transverse dimension `2` instead of `3`. -/
structure NullCongruence (L : ℝ) where
  theta : ℝ → ℝ
  dtheta : ℝ → ℝ
  hderiv : ∀ τ ∈ Set.Ico (0 : ℝ) L, HasDerivAt theta (dtheta τ) τ
  hRay : ∀ τ ∈ Set.Ico (0 : ℝ) L, dtheta τ ≤ -(theta τ) ^ 2 / 2
  htrapped : theta 0 < 0

/-- **Penrose (null) focusing lemma**: only the numerical constant differs. -/
