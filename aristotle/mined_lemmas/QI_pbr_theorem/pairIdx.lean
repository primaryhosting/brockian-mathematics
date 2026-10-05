/-
# Pbr Theorem
Category: Frontier Qi
Target: QI.pbr_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Pbr Theorem
Category: Frontier Qi
Target: QI.pbr_theorem
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

set_option grind.warning false

namespace QI

open MeasureTheory MeasureTheory.Measure Complex

noncomputable section

/-! ## The quantum input: the Pusey–Barrett–Rudolph measurement on two qubits -/

/-- The real number `1/√2`, viewed as a complex amplitude. -/

def pairIdx : Fin 2 → Fin 2 → Fin 4 := ![![0, 1], ![2, 3]]

/-- The PBR measurement is a genuine projective measurement: its four vectors are orthonormal,
hence an orthonormal basis of `ℂ⁴`. -/
