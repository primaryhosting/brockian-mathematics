/-!
# Pauli Exclusion Antisym
Category: Quantum Physics
Target: QPhys.pauli_exclusion_antisym
Statement: A two-fermion antisymmetric state with equal single-particle states is zero.
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-!
# Pauli exclusion principle: an antisymmetric two-fermion state with equal
single-particle states vanishes.

`H` is the (complex, or general) single-particle state space, a vector space over
a field `𝕜` of characteristic different from `2`.  A two-fermion state is a
`M`-valued function `Ψ : H → H → M` of the two single-particle states, and the
fermionic (antisymmetry) requirement is `Ψ u v = - Ψ v u`.  The main theorem
`QPhys.pauli_exclusion_antisym` states that such a state vanishes whenever the
two single-particle states coincide.

Concrete incarnations are given afterwards: the Slater-determinant state
`u ⊗ v - v ⊗ u` inside `H ⊗[𝕜] H`, and the wedge product inside the exterior
algebra.
-/

namespace QPhys

variable {𝕜 H M : Type*} [Field 𝕜] [AddCommGroup H] [Module 𝕜 H]
  [AddCommGroup M] [Module 𝕜 M]

omit [AddCommGroup H] [Module 𝕜 H] in
/-- **Pauli exclusion principle (antisymmetry form).**
A two-fermion state `Ψ`, i.e. a state depending antisymmetrically on the two
single-particle states, is zero when the two single-particle states are equal.
(The characteristic of the scalar field must differ from `2`, otherwise
antisymmetry is no restriction at all.) -/
theorem pauli_exclusion_antisym (h2 : (2 : 𝕜) ≠ 0) (Psi : H → H → M)
    (hanti : ∀ u v, Psi u v = - Psi v u) (u : H) : Psi u u = 0 := by
  have h : Psi u u = - Psi u u := hanti u u
  have h2' : (2 : 𝕜) • Psi u u = 0 := by
    rw [two_smul]
    nth_rewrite 2 [h]
    exact add_neg_cancel _
  rcases smul_eq_zero.mp h2' with h3 | h3
  · exact absurd h3 h2
  · exact h3

/-- The antisymmetrized (Slater-determinant) two-particle state built from the
single-particle states `u` and `v`. -/
noncomputable def slater (𝕜 : Type*) [Field 𝕜] {H : Type*} [AddCommGroup H]
    [Module 𝕜 H] (u v : H) : TensorProduct 𝕜 H H :=
  u ⊗ₜ[𝕜] v - v ⊗ₜ[𝕜] u

/-- The Slater state is antisymmetric under exchange of the two particles. -/
theorem slater_antisymm (u v : H) : slater 𝕜 u v = - slater 𝕜 v u := by
  simp [slater]

/-- Pauli exclusion for the Slater two-particle state: two fermions cannot
occupy the same single-particle state. -/
theorem slater_self (u : H) : slater 𝕜 u u = 0 :=
  sub_self _

/-- Pauli exclusion in the exterior-algebra (wedge product) formulation:
`u ∧ u = 0`. -/
theorem wedge_self (u : H) :
    (ExteriorAlgebra.ι 𝕜 u) * (ExteriorAlgebra.ι 𝕜 u) = 0 :=
  ExteriorAlgebra.ι_sq_zero u

/-- If the pure two-particle state `ψ ⊗ ψ` is antisymmetric under exchange of
the particles, then it is zero. -/
theorem tmul_self_of_antisymm (h2 : (2 : 𝕜) ≠ 0) (psi : H)
    (h : TensorProduct.comm 𝕜 H H (psi ⊗ₜ[𝕜] psi) = - (psi ⊗ₜ[𝕜] psi)) :
    psi ⊗ₜ[𝕜] psi = (0 : TensorProduct 𝕜 H H) := by
  rw [TensorProduct.comm_tmul] at h
  have h2' : (2 : 𝕜) • (psi ⊗ₜ[𝕜] psi : TensorProduct 𝕜 H H) = 0 := by
    rw [two_smul]
    nth_rewrite 2 [h]
    exact add_neg_cancel _
  rcases smul_eq_zero.mp h2' with h3 | h3
  · exact absurd h3 h2
  · exact h3

end QPhys

#print axioms QPhys.pauli_exclusion_antisym
#print axioms QPhys.slater_self
#print axioms QPhys.wedge_self
#print axioms QPhys.tmul_self_of_antisymm

