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

lemma inner4_expand (x y : Fin 2 × Fin 2 → ℂ) :
    inner4 x y =
      (starRingEnd ℂ) (x (0,0)) * y (0,0) + (starRingEnd ℂ) (x (0,1)) * y (0,1)
      + ((starRingEnd ℂ) (x (1,0)) * y (1,0) + (starRingEnd ℂ) (x (1,1)) * y (1,1)) := by
  simp [inner4, Fintype.sum_prod_type, Fin.sum_univ_two]

/-- **Key quantum fact.** Each PBR outcome has zero Born probability on the
corresponding product preparation: the PBR basis vector `ξ_k` is orthogonal to
`prep b₁ ⊗ prep b₂` where `(b₁, b₂) = excluded k`. -/
