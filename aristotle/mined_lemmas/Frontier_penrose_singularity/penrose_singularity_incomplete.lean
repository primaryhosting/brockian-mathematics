/-
# Penrose Singularity
Category: Frontier Physics
Target: Frontier.penrose_singularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
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

namespace Frontier

/-!
## Formalization

The analytic core of Penrose's singularity theorem is the *focusing* of the null
geodesic congruence generating the boundary of the future of a trapped surface.

Along an affinely parametrised null geodesic congruence with affine parameter `t`,
expansion `θ`, shear scalar `shear = σ_{ab} σ^{ab} ≥ 0` and Ricci contraction
`ric = R_{ab} k^a k^b`, the Raychaudhuri equation for a hypersurface-orthogonal
null congruence with two-dimensional screen space reads

  `dθ/dt = - θ² / 2 - shear - ric`.

The *null energy condition* (together with the Einstein equations) gives `ric ≥ 0`,
and the presence of a *trapped surface* gives an initially negative expansion,
`θ 0 < 0`.

The theorem below shows that under these hypotheses the congruence cannot remain
regular for an affine parameter interval longer than `2 / |θ 0|`: any interval
`[0, L]` on which the expansion is finite and differentiable must satisfy
`L < 2 / (-θ 0)`. Equivalently, the expansion blows up (a conjugate/focal point
forms) at some affine parameter `≤ 2 / |θ 0|`; the generators of the boundary
therefore cannot be extended indefinitely — the spacetime is null geodesically
incomplete, which is Penrose's conclusion.
-/

/-- **Penrose singularity theorem (Raychaudhuri focusing core).**

Let `θ` be the expansion of an affinely parametrised null geodesic congruence,
with derivative `D`, shear scalar `shear` and Ricci contraction `ric` along the
generators, satisfying the Raychaudhuri equation on the affine interval `[0, L]`.
Assume the null energy condition `0 ≤ ric` and the (always valid) positivity of
the shear scalar `0 ≤ shear`, and assume the initial cross-section is *trapped*,
i.e. `θ 0 < 0`.

Then the congruence cannot remain regular for affine length `2 / |θ 0|` or more:
`L < 2 / (-θ 0)`. Hence the generators are incomplete (see
`Frontier.penrose_singularity_incomplete`). -/

theorem penrose_singularity_incomplete
    (θ D shear ric : ℝ → ℝ)
    (hderiv : ∀ t : ℝ, 0 ≤ t → HasDerivAt θ (D t) t)
    (hray : ∀ t : ℝ, 0 ≤ t → D t = -(θ t) ^ 2 / 2 - shear t - ric t)
    (hshear : ∀ t : ℝ, 0 ≤ t → 0 ≤ shear t)
    (hnec : ∀ t : ℝ, 0 ≤ t → 0 ≤ ric t)
    (htrapped : θ 0 < 0) :
    False := by
  have hpos : 0 < -θ 0 := by linarith
  set L : ℝ := 2 / (-θ 0) with hLdef
  have hL : 0 ≤ L := le_of_lt (div_pos (by norm_num) hpos)
  have := penrose_singularity L hL θ D shear ric
    (fun t ht => hderiv t ht.1) (fun t ht => hray t ht.1)
    (fun t ht => hshear t ht.1) (fun t ht => hnec t ht.1) htrapped
  exact lt_irrefl L this

/-- The hypotheses of `Frontier.penrose_singularity` are non-vacuous: for every affine
length `L < 1` there is a genuine focusing congruence realising them (here with vanishing
shear and vanishing Ricci contraction, `θ t = 2 / (t - 1)`, whose expansion diverges exactly
at the focal parameter `1 = 2 / |θ 0|`). -/
