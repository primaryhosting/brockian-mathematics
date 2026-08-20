import Mathlib

/-!
# Penrose Singularity
Category: Frontier Physics
Target: Frontier.penrose_singularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` lines to precede every other command, so the header comment
-- above is placed immediately after the single `import Mathlib` line.)

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

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types false
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-!
## The analytic core: Raychaudhuri focusing

For a null geodesic congruence with vanishing shear and rotation (as holds for the
generators of the boundary of the causal future of a surface), the Raychaudhuri equation
together with the null energy condition `Ric(k,k) ≥ 0` gives the differential inequality

  `θ' ≤ - θ² / 2`

for the expansion `θ` as a function of the affine parameter. The following theorem is the
exact analytic content of the focusing argument: a solution of this inequality with
`θ 0 < 0` blows up (i.e. cannot be continued) before affine parameter `2 / |θ 0|`.
-/

/-- **Raychaudhuri focusing theorem.**  If `θ` satisfies the null-energy-condition
inequality `θ' ≤ -θ²/2` on `[0, L]` and starts out converging, `θ 0 < 0`, then
`L < 2 / (-θ 0)`.  Equivalently: a congruence with initially negative expansion develops a
focal point within affine parameter `2 / |θ 0|`. -/

theorem penrose_singularity (C : TrappedSurfaceCongruence) :
    ¬ NullGeodesicallyComplete C := by
  intro hcomplete
  obtain ⟨s⟩ := C.gen_nonempty
  have hpos : 0 < 2 / C.focusConst := div_pos (by norm_num) C.focusConst_pos
  have hT : C.Extends s (2 / C.focusConst) := hcomplete s _ (le_of_lt hpos)
  exact absurd (affineLength_lt_of_extends C hT) (lt_irrefl _)

/-- Restatement: such a spacetime is null geodesically incomplete. -/
