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

def pbrVec : Fin 4 → (Fin 2 × Fin 2 → ℂ) :=
  ![fun p => !![0, rt; rt, 0] p.1 p.2,
    fun p => !![1/2, -(1/2); 1/2, 1/2] p.1 p.2,
    fun p => !![1/2, 1/2; -(1/2), 1/2] p.1 p.2,
    fun p => !![rt, 0; 0, -rt] p.1 p.2]

/-- The preparation pair whose Born probability for the corresponding PBR
outcome vanishes: outcome `k` is impossible for the preparation `excluded k`. -/
