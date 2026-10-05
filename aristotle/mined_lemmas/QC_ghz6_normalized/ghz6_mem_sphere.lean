/-
# Ghz 6 Normalized
Category: Quantum Computing
Target: QC.ghz6_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Ghz 6 Normalized
Category: Quantum Computing
Target: QC.ghz6_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean 4 requires `import` commands to precede every other command, including
-- module docstrings (`/-! ... -/`).  The header therefore appears twice: as a plain
-- block comment at the very top of the file, and as the module docstring below the
-- import.  The text is otherwise identical.

namespace QC

/-- The all-zeros basis label `|000000⟩` of a 6-qubit register. -/

theorem ghz6_mem_sphere : ghz6 ∈ Metric.sphere (0 : EuclideanSpace ℂ (Fin 6 → Bool)) 1 := by
  simpa [mem_sphere_iff_norm] using ghz6_normalized

end QC

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

