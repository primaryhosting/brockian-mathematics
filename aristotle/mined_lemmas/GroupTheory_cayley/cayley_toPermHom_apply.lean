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
# Cayley
Category: Frontier Wave 2 (deeper machinery)
Target: GroupTheory.cayley
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Cayley
Category: Frontier Wave 2 (deeper machinery)
Target: GroupTheory.cayley
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace GroupTheory

/-- **Cayley's theorem**: every group `G` admits an injective group homomorphism into the
symmetric group `Equiv.Perm G` on its underlying set.

The embedding is `MulAction.toPermHom G G`, sending `g` to left multiplication by `g`, viewed as
a permutation of `G`. Injectivity is `MulAction.toPerm_injective`, available since the left
translation action of `G` on itself is faithful. -/

theorem cayley_toPermHom_apply (G : Type*) [Group G] (g x : G) :
    MulAction.toPermHom G G g x = g * x := rfl

end GroupTheory

