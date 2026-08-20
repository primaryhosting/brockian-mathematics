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

/-!
## Setting

The analytic core of Penrose's singularity theorem is the focusing of a null geodesic
congruence.  Along a null generator of the boundary of the future of a closed trapped
surface, with affine parameter `t`, the expansion `θ` of the congruence satisfies the
Raychaudhuri equation

  `dθ/dt = -θ² / 2 - σ_{ab}σ^{ab} - R_{ab} k^a k^b`,

where `σ` is the shear and `k` is the null tangent.  The null energy condition gives
`R_{ab} k^a k^b ≥ 0`, and the shear term is nonnegative, so the *Raychaudhuri inequality*

  `dθ/dt ≤ -θ² / 2`

holds.  That the surface is *trapped* means precisely that the initial expansion of the
outgoing null congruence is negative: `θ 0 < 0`.

The structure `NullGeneratorData L` below packages exactly this data on an affine
interval `[0, L]`: the expansion along a null generator that is defined (and
differentiable, with finite expansion) for affine parameter in `[0, L]`, satisfying the
Raychaudhuri inequality, and emanating from a trapped surface.

The theorem `Frontier.penrose_singularity` states that such a generator can only exist for
affine length `L < 2 / |θ 0|`: the null geodesic congruence focuses to a conjugate point in
finite affine parameter, so the generator cannot be extended, i.e. the spacetime is null
geodesically incomplete (`Frontier.penrose_null_geodesic_incomplete`).
-/

/-- Data of a null geodesic generator, parametrized by affine parameter in `[0, L]`,
issuing orthogonally from a closed trapped surface, in a spacetime satisfying the null
energy condition.

* `expansion` is the expansion scalar `θ` of the null congruence;
* `expansionDeriv` is its derivative with respect to the affine parameter;
* `raychaudhuri` is the Raychaudhuri inequality `θ' ≤ -θ²/2`, which follows from the
  Raychaudhuri equation together with the null energy condition and the nonnegativity of
  the shear term;
* `trapped` says that the surface is trapped: the initial expansion is negative. -/
structure NullGeneratorData (L : ℝ) where
  /-- The expansion scalar `θ` of the null congruence along the generator. -/
  expansion : ℝ → ℝ
  /-- The derivative of the expansion with respect to the affine parameter. -/
  expansionDeriv : ℝ → ℝ
  /-- The expansion is differentiable in the affine parameter on `[0, L]`
  (in particular it stays finite there: no conjugate point occurs on `[0, L]`). -/
  hasDeriv : ∀ t ∈ Set.Icc (0 : ℝ) L, HasDerivAt expansion (expansionDeriv t) t
  /-- Raychaudhuri inequality, a consequence of the null energy condition. -/
  raychaudhuri : ∀ t ∈ Set.Icc (0 : ℝ) L, expansionDeriv t ≤ -(expansion t) ^ 2 / 2
  /-- Trapped surface condition: the initial expansion is negative. -/
  trapped : expansion 0 < 0

namespace NullGeneratorData

variable {L : ℝ} (C : NullGeneratorData L)

/-- The expansion is nonincreasing along the generator. -/

theorem monotoneOn_aux : MonotoneOn C.aux (Set.Icc 0 L) := by
  refine monotoneOn_of_deriv_nonneg (convex_Icc 0 L) ?_ ?_ ?_
  · exact fun t ht => (C.hasDerivAt_aux ht).continuousAt.continuousWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    exact ((C.hasDerivAt_aux (Set.mem_Icc_of_Ioo ht)).differentiableAt).differentiableWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    have ht' : t ∈ Set.Icc (0 : ℝ) L := Set.mem_Icc_of_Ioo ht
    rw [(C.hasDerivAt_aux ht').deriv]
    have hneg : C.expansion t < 0 := C.expansion_neg ht'
    have hsq : 0 < (C.expansion t) ^ 2 := by nlinarith
    have hR : C.expansionDeriv t ≤ -(C.expansion t) ^ 2 / 2 := C.raychaudhuri t ht'
    rw [sub_nonneg, le_div_iff₀ hsq]
    linarith

end NullGeneratorData

/-- **Penrose singularity theorem (focusing core).**

In a spacetime satisfying the null energy condition, a null geodesic generator issuing
from a closed trapped surface (so that the Raychaudhuri inequality `θ' ≤ -θ²/2` holds and
the initial expansion `θ 0` is negative) cannot remain regular for affine parameter
beyond `2 / |θ 0|`: any interval `[0, L]` on which the congruence is defined with finite
expansion satisfies `L < 2 / |θ 0|`.

Thus the generator reaches a conjugate (focal) point within affine parameter `2 / |θ 0|`,
which is the analytic heart of Penrose's theorem: together with compactness of the trapped
surface and the global hyperbolicity/non-compact Cauchy surface hypothesis, it forces null
geodesic incompleteness. -/
