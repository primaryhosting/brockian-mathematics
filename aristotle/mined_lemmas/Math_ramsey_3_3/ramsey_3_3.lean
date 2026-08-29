/-!
# Ramsey 3 3
Category: Pure Mathematics
Target: Math.ramsey_3_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- An auxiliary "vector" of five booleans, read off as a function on `Fin 6` (the value at
the index `0` is irrelevant and set to `false`). -/

theorem ramsey_3_3 :
    (∀ c : Fin 6 → Fin 6 → Bool, (∀ i j, c i j = c j i) →
        ∃ a b d : Fin 6, a ≠ b ∧ a ≠ d ∧ b ≠ d ∧ c a b = c a d ∧ c a b = c b d) ∧
    (∃ c : Fin 5 → Fin 5 → Bool, (∀ i j, c i j = c j i) ∧
        ∀ a b d : Fin 5, a ≠ b → a ≠ d → b ≠ d → ¬(c a b = c a d ∧ c a b = c b d)) := by
  refine ⟨fun c _ => mono_triangle_of_six c, pentagon, by decide, by decide⟩

end Math

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

