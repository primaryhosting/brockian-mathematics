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

open Set

/-!
## The Raychaudhuri focusing theorem

The analytic heart of Penrose's singularity theorem is the following statement about the
expansion `θ` of a null geodesic congruence, as a function of the affine parameter `t`.

Along a hypersurface-orthogonal null geodesic congruence with tangent field `k`, the
Raychaudhuri equation reads

  `dθ/dt = -θ²/2 - σ_{ab}σ^{ab} - R_{ab} k^a k^b`,

where `σ_{ab}σ^{ab} ≥ 0` is the squared shear (the twist vanishes by hypersurface
orthogonality) and `R_{ab} k^a k^b ≥ 0` is the null energy condition (via the Einstein
equations, equivalently the null convergence condition).

Consequently `dθ/dt ≤ -θ²/2`, and if the congruence starts on a *trapped surface*, i.e.
`θ 0 < 0`, then `θ` reaches `-∞` (a focal point) within affine parameter `2/|θ 0|`.
So the congruence cannot be defined on any longer affine interval: the null geodesics are
incomplete (or hit a focal point, which in Penrose's global argument is what contradicts
the existence of a noncompact Cauchy surface).
-/

/-- **Focusing lemma.** If the expansion `θ` of a null congruence is defined and
differentiable on the affine interval `[0, L]` and satisfies the Raychaudhuri inequality
`θ' ≤ -θ²/2` there, and if the initial cross-section is trapped (`θ 0 < 0`), then
`L < 2 / |θ 0|`.  In particular no such congruence survives past affine parameter
`2 / |θ 0|`. -/

def CompleteNullCongruence.Trapped (C : CompleteNullCongruence) : Prop :=
  C.expansion 0 < 0

/-- **Penrose singularity theorem (focusing form).**

A spacetime containing a trapped surface and satisfying the null energy condition is null
geodesically incomplete: there is no null geodesic congruence orthogonal to the trapped
surface that is complete (defined for all affine parameters `t ≥ 0`) and obeys the
Raychaudhuri equation with nonnegative shear and nonnegative null-null Ricci curvature.

This is the contrapositive formulation: the assumptions of completeness, the null energy
condition, and the existence of a trapped cross-section are jointly contradictory.  The
proof is the Raychaudhuri focusing estimate `raychaudhuri_focusing`: the expansion must
blow up before affine parameter `2/|θ 0|`, so the congruence cannot extend that far. -/
