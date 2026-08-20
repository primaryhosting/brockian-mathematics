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
# Variational Bound
Category: Quantum Physics
Target: QPhys.variational_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QPhys

open scoped ComplexConjugate

variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- Action of the Hamiltonian on a basis vector, tested against `ψ`:
if `H` has orthonormal eigenbasis `b` with (real) eigenvalues `E`, then
`⟪bᵢ, Hψ⟫ = Eᵢ ⟪bᵢ, ψ⟫`. -/

lemma norm_sq_expansion (b : OrthonormalBasis (Fin n) ℂ V) (ψ : V) :
    ‖ψ‖ ^ 2 = ∑ i, ‖inner ℂ (b i) ψ‖ ^ 2 := by
  rw [← b.repr.norm_map ψ, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp [b.repr_apply_apply]

/-- **Variational bound (Rayleigh–Ritz), normalized form.**
Same as `QPhys.variational_bound`, with the denominator written as `‖ψ‖ ^ 2`. -/
