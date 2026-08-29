/-!
# Cantor No Injection From Powerset
Category: Frontier — Set Theory
Target: Infinity.cantor_no_injection_from_powerset
Statement: Dual Cantor: for any type X, no function g : Set X -> X is injective. (Use Mathlib's Function.cantor_injective.)
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Infinity

/-- Dual Cantor theorem: for any type `X`, no function `g : Set X → X` is injective. -/
theorem cantor_no_injection_from_powerset {X : Type*} (g : Set X → X) :
    ¬ Function.Injective g :=
  Function.cantor_injective g

end Infinity

