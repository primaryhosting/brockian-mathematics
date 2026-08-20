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

/-
# Equidistribution Of Transitive Symmetry
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionUniformity.equidistribution_of_transitive_symmetry
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: the header is a plain block comment rather than a module docstring, because in Lean 4 a
module docstring may not appear before the `import` line.)
-/

import Mathlib

namespace Brockian
namespace EquidistributionUniformity

/-- A real-valued weight function invariant under a transitive group action is constant. -/

theorem equidistribution_of_isPretransitive {G X : Type*} [Group G] [Fintype X]
    [MulAction G X] [MulAction.IsPretransitive G X]
    (w : X → ℝ) (hinv : ∀ (g : G) (x : X), w (g • x) = w x)
    (hsum : ∑ x, w x = 1) :
    ∀ x : X, w x = 1 / (Fintype.card X : ℝ) :=
  equidistribution_of_transitive_symmetry
    (fun x y => MulAction.exists_smul_eq G x y) w hinv hsum

end EquidistributionUniformity
end Brockian

