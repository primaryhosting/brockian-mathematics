/-
# No Deleting
Category: Frontier Qi
Target: QI.no_deleting
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# No Deleting
Category: Frontier Qi
Target: QI.no_deleting
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

The no-deleting theorem states that, given two copies of an unknown quantum state,
there is no unitary evolution that deletes one of the copies (sending it to a fixed
"blank" state) while leaving the ancilla in a fixed final state.

We model a qubit by `EuclideanSpace ℂ (Fin 2)`, an ancilla by `EuclideanSpace ℂ α`
for an arbitrary finite index type `α`, and the tensor product of state vectors by
`QI.tens` (the Kronecker product of coordinate vectors, which is the standard
concrete model of the tensor product of finite-dimensional Hilbert spaces).

A unitary is modelled as a `ℂ`-linear isometric equivalence `U`.  The key facts used
are that `U` preserves inner products and that the inner product is multiplicative
with respect to `tens`.
-/

namespace QI

open scoped ComplexConjugate

/-- The Kronecker (tensor) product of two finite-dimensional state vectors. -/

theorem inner_ket0_ketPlus_sq_ne : inner ℂ ket0 ketPlus * inner ℂ ket0 ketPlus
    ≠ inner ℂ ket0 ketPlus := by
  rw [inner_ket0_ketPlus]
  intro h
  have h2 : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hr : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (Real.sqrt 2)⁻¹ := by exact_mod_cast h
  have hr' : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = 1 * (Real.sqrt 2)⁻¹ := by
    rw [one_mul]; exact hr
  have h1 : (Real.sqrt 2)⁻¹ = 1 := mul_right_cancel₀ (inv_ne_zero h2.ne') hr'
  have h3 : Real.sqrt 2 = 1 := by field_simp at h1; exact h1.symm
  have h4 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  rw [h3] at h4
  norm_num at h4

/-- **No-deleting theorem.**  Let `blank` be a fixed blank qubit state, `anc` a fixed
initial ancilla state and `out` a fixed final ancilla state (all unit vectors).  There is
no unitary `U` on `qubit ⊗ qubit ⊗ ancilla` that maps `|ψ⟩ ⊗ |ψ⟩ ⊗ |anc⟩` to
`|ψ⟩ ⊗ |blank⟩ ⊗ |out⟩` for every unknown (unit) qubit state `ψ`: i.e. no unitary can
delete one of two copies of an unknown quantum state. -/
