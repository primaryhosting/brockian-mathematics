/-
# Pbr Theorem
Category: Frontier Qi
Target: QI.pbr_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring, so the required
-- header appears above as a plain comment and again below as a docstring.)

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
open scoped Classical

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace QI

noncomputable section

/-! ## The quantum ingredients

We work with two qubits, i.e. with the space of functions `Fin 2 × Fin 2 → ℂ`,
equipped with the standard Hermitian inner product. -/

/-- The standard Hermitian inner product on the two-qubit space. -/

def inner4 (x y : Fin 2 × Fin 2 → ℂ) : ℂ :=
  ∑ p : Fin 2 × Fin 2, (starRingEnd ℂ) (x p) * y p

/-- `1/√2`, as a complex number. -/
