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

theorem no_complete_congruence_of_negative_expansion {n τ₀ : ℝ} {theta dtheta : ℝ → ℝ}
    (hn : 0 < n) (hderiv : ∀ τ : ℝ, 0 ≤ τ → HasDerivAt theta (dtheta τ) τ)
    (hRay : ∀ τ : ℝ, 0 ≤ τ → dtheta τ ≤ -(theta τ) ^ 2 / n)
    (hτ₀ : 0 ≤ τ₀) (hneg : theta τ₀ < 0) : False := by
  set g : ℝ → ℝ := fun s => theta (τ₀ + s) with hg
  set dg : ℝ → ℝ := fun s => dtheta (τ₀ + s) with hdg
  set L : ℝ := -n / theta τ₀ + 1 with hL
  have hgderiv : ∀ s ∈ Ico (0 : ℝ) L, HasDerivAt g (dg s) s := by
    intro s hs
    have hs0 : 0 ≤ τ₀ + s := by linarith [hs.1]
    have h := (hderiv (τ₀ + s) hs0).comp s ((hasDerivAt_id s).const_add τ₀)
    simpa [hg, hdg, Function.comp] using h
  have hgRay : ∀ s ∈ Ico (0 : ℝ) L, dg s ≤ -(g s) ^ 2 / n := by
    intro s hs
    exact hRay (τ₀ + s) (by linarith [hs.1])
  have hg0 : g 0 < 0 := by simpa [hg] using hneg
  have hbound := raychaudhuri_focusing_general hn hgderiv hgRay hg0
  simp only [hg, add_zero] at hbound
  rw [hL] at hbound
  linarith

/-! ### The timelike (Hawking) packaging -/

/-- Timelike expansion of a vorticity-free congruence on a proper-time interval `[0, L)`
in `3 + 1` dimensions.  `hRay` is the Raychaudhuri inequality: it encodes the strong
energy condition (`Ric(u,u) ≥ 0`), vanishing vorticity and the trace inequality
`σ_{ab}σ^{ab} ≥ 0`.  `htrapped` says the congruence is initially converging. -/
structure TimelikeCongruence (L : ℝ) where
  theta : ℝ → ℝ
  dtheta : ℝ → ℝ
  hderiv : ∀ τ ∈ Set.Ico (0 : ℝ) L, HasDerivAt theta (dtheta τ) τ
  hRay : ∀ τ ∈ Set.Ico (0 : ℝ) L, dtheta τ ≤ -(theta τ) ^ 2 / 3
  htrapped : theta 0 < 0

/-- **Hawking focusing lemma.**  A vorticity-free timelike congruence in `3 + 1`
dimensions with initial expansion `theta 0 < 0` develops a conjugate point within proper
time `-3 / theta 0`; equivalently, the length of an interval carrying such a congruence
is at most `-3 / theta 0`.

(The hypothesis `0 < L` of the original sketch is not needed: for `L ≤ 0` the bound holds
trivially since `-3 / theta 0 > 0`.) -/
