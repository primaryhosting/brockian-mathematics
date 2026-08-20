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

namespace Frontier

/-!
## Setting

Mathlib does not (yet) contain Lorentzian causal theory, so the Penrose singularity

theorem is formalised here at the level of its analytic core, the *Raychaudhuri
focusing argument*, which is where the null energy condition and the trapped-surface
hypothesis actually enter.

Consider the congruence of future-directed null geodesics orthogonal to a smooth
closed spacelike surface `S`, parametrised by an affine parameter `t ≥ 0`, and let
`theta t` be the expansion of the congruence at affine parameter `t`.  The
Raychaudhuri equation for a hypersurface-orthogonal (hence vorticity-free) null
congruence in a `4`-dimensional spacetime reads

  `theta' = -theta ^ 2 / 2 - shear ^ 2 - Ric(k, k)`,

where `k` is the null tangent.  The null energy condition gives `Ric(k, k) ≥ 0` and
the shear term is a sum of squares, so the whole physical input is captured by the
differential inequality

  `theta' ≤ -theta ^ 2 / 2`.

`S` being a *trapped surface* means precisely that the initial expansion of the
(outgoing as well as ingoing) orthogonal null congruence is negative, `theta 0 < 0`.

The theorem below shows that these hypotheses force the affine parameter range of
the congruence to be *bounded*, by `-2 / theta 0`: a conjugate point (a focal point
of `S`) is reached at or before that affine parameter, so the null geodesics of the
congruence cannot be extended to arbitrarily large affine parameter, i.e. the
spacetime is null geodesically incomplete.
-/

/-- The expansion data of the future-directed null geodesic congruence orthogonal to a
closed spacelike surface, defined on the affine parameter interval `[0, L)`.

* `theta t` is the expansion at affine parameter `t`;
* `dtheta t` is its derivative;
* `raychaudhuri` is the Raychaudhuri equation combined with the null energy condition
  and vanishing vorticity: `theta' ≤ -theta ^ 2 / 2`. -/
structure NullCongruence (L : ℝ) where
  /-- Expansion of the congruence as a function of the affine parameter. -/
  theta : ℝ → ℝ
  /-- Derivative of the expansion with respect to the affine parameter. -/
  dtheta : ℝ → ℝ
  /-- `dtheta` really is the derivative of `theta` on the affine parameter range. -/
  hasDerivAt : ∀ t ∈ Set.Ico (0 : ℝ) L, HasDerivAt theta (dtheta t) t
  /-- Raychaudhuri's equation together with the null energy condition (`Ric (k, k) ≥ 0`)
  and vanishing vorticity. -/
  raychaudhuri : ∀ t ∈ Set.Ico (0 : ℝ) L, dtheta t ≤ -(theta t) ^ 2 / 2

/-- A surface is *trapped* (for this congruence) when the initial expansion of the
orthogonal null congruence is negative. -/
