import Mathlib
/-!
# Cantor No Injection From Powerset
Category: Frontier — Set Theory
Target: Infinity.cantor_no_injection_from_powerset
Verification: verified (axiom-clean: propext, Quot.sound)
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Infinity

/-- **Dual Cantor theorem**: for any type `X`, no map `g : Set X → X` is injective.

(The `import Mathlib` line must precede the header comment: Lean 4 requires all `import`
commands to appear before any other content, including module documentation.) -/
theorem cantor_no_injection_from_powerset {X : Type*} (g : Set X → X) :
    ¬ Function.Injective g :=
  Function.cantor_injective g

end Infinity

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

