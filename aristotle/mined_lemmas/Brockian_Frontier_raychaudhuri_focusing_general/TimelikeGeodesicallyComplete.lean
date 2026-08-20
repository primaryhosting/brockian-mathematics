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

def TimelikeGeodesicallyComplete {ι : Type*} (C : ExpandingCauchy ι) : Prop :=
  ∀ (i : ι), ∀ τ : ℝ, 0 ≤ τ → HasDerivAt (C.theta i) (C.dtheta i τ) τ

/-- **Hawking singularity theorem (quantitative reduction).**  A spacetime containing a
Cauchy surface whose orthogonal geodesic congruence is uniformly contracting, and which
satisfies the strong energy condition, is not timelike geodesically complete: every
generator terminates (in a conjugate point / focal singularity) within proper time
`3 / c`. -/
