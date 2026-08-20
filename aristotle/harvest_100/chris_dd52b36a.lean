import Mathlib

/-!
# Completed Symmetry Half
Category: Riemann Program
Target: Riemann.functional.completed_symmetry_half
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean 4 requires `import` commands to precede every other command, including
-- module doc comments (`/-! ... -/`), so the required header appears immediately after
-- the single `import Mathlib` line, with its text reproduced verbatim.

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

namespace Riemann
namespace functional

/-- **Completed symmetry at the center of the critical strip.**

The completed Riemann zeta function `Λ` satisfies the functional equation
`Λ (1 - s) = Λ s` (`completedRiemannZeta_one_sub` in Mathlib). At the fixed point
`s = 1/2` of `s ↦ 1 - s` this is trivially self-consistent, since `1 - 1/2 = 1/2`
as complex numbers. -/
theorem completed_symmetry_half :
    completedRiemannZeta (1 - (1 / 2 : ℂ)) = completedRiemannZeta (1 / 2 : ℂ) :=
  completedRiemannZeta_one_sub (1 / 2 : ℂ)

/-- The same statement, proved directly from `1 - 1/2 = 1/2` rather than from the
functional equation. -/
example :
    completedRiemannZeta (1 - (1 / 2 : ℂ)) = completedRiemannZeta (1 / 2 : ℂ) := by
  norm_num

end functional
end Riemann

