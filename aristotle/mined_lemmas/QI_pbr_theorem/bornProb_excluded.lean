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

theorem bornProb_excluded (k : Fin 4) :
    bornProb k (excluded k).1 (excluded k).2 = 0 := by
  fin_cases k <;>
    simp only [bornProb, excluded, inner4_expand, pbrVec, tens, prep, ket0, ketPlus] <;>
    norm_num [conj_rt]

/-! ### The PBR basis is an orthonormal basis

These facts are not needed for the main theorem, but they certify that the
four response functions of an ontological model really do come from a genuine
projective measurement on the two-qubit space. -/

