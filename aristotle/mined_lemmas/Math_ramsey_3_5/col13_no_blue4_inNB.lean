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
# Ramsey 3 5
Category: Pure Mathematics
Target: Math.ramsey_3_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Ramsey 3 5
Category: Pure Mathematics
Target: Math.ramsey_3_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- `Mono c col S` says that the finite set `S` is monochromatic of colour `col`
for the edge-colouring `c` : every pair of distinct vertices of `S` gets colour `col`. -/

theorem col13_no_blue4_inNB : ∀ p q r s : Fin 13, inNB p → inNB q → inNB r → inNB s →
    p ≠ q → p ≠ r → p ≠ s → q ≠ r → q ≠ s → r ≠ s →
    ¬(col13 p q = false ∧ col13 p r = false ∧ col13 p s = false ∧ col13 q r = false ∧
      col13 q s = false ∧ col13 r s = false) := by decide

set_option maxRecDepth 100000 in
