import Brockian.Weyl.DeficiencyODE

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

import Mathlib

/-!
# Essential self-adjointness of Schrödinger operators via deficiency indices

This file develops, from scratch:

* a minimal framework for (possibly unbounded) operators on a complex Hilbert space,
  given as a linear map `T : D →ₗ[ℂ] H` out of a submodule `D` of `H`, together with
  their graphs, adjoint graphs, symmetry and essential self-adjointness;
* the *basic criterion* of essential self-adjointness: a densely defined symmetric
  operator whose deficiency spaces `ker (T* ∓ i)` are trivial is essentially
  self-adjoint;
* the deficiency ("Weyl limit point") analysis of the second order difference
  equation attached to a discrete Schrödinger operator, and the resulting
  essential self-adjointness of the discrete Schrödinger operator
  `(T u) n = u (n-1) + u (n+1) + V n * u n` on `ℓ²(ℤ, ℂ)`, defined on the
  (dense) span of the standard basis vectors, for an **arbitrary** real potential
  `V : ℤ → ℝ`.

The main theorem
`schrodinger_essentiallySelfAdjoint_of_weakRegularity` is unconditional: no regularity
(or boundedness) hypothesis on the potential is needed, so the classical weak regularity
assumption is discharged. Everything is proved from first principles on top of Mathlib;
in particular the framework for unbounded operators, their adjoints and essential
self-adjointness is built here.
-/

open scoped InnerProductSpace ComplexConjugate

namespace Brockian.Weyl.DeficiencyODE

/-! ## An abstract framework for unbounded operators -/

section Abstract

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The graph of an operator `T` defined on the submodule `D` of `H`. -/

lemma inner_self_symm_of_mem_closure {D : Submodule ℂ H} {T : D →ₗ[ℂ] H}
    (h : IsSymmetricOp D T) {p : H × H} (hp : p ∈ (opGraph D T).topologicalClosure) :
    ⟪p.2, p.1⟫_ℂ = ⟪p.1, p.2⟫_ℂ := by
  have hsub : ((opGraph D T : Submodule ℂ (H × H)) : Set (H × H))
      ⊆ {q : H × H | ⟪q.2, q.1⟫_ℂ = ⟪q.1, q.2⟫_ℂ} := by
    rintro q ⟨u, rfl⟩
    exact h u u
  have hclosed : IsClosed {q : H × H | ⟪q.2, q.1⟫_ℂ = ⟪q.1, q.2⟫_ℂ} :=
    isClosed_eq (continuous_snd.inner continuous_fst) (continuous_fst.inner continuous_snd)
  have hmin := closure_minimal hsub hclosed
  have hp' : p ∈ closure ((opGraph D T : Submodule ℂ (H × H)) : Set (H × H)) := by
    rw [← Submodule.topologicalClosure_coe]
    exact hp
  exact hmin hp'

/-- If `⟪w, u⟫` is real and `z` is purely imaginary of modulus one, then
`‖w + z • u‖ ^ 2 = ‖w‖ ^ 2 + ‖u‖ ^ 2`. -/
