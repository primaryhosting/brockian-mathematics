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

theorem inner_adjGraph_symm {D : Submodule ℂ H} {T : D →ₗ[ℂ] H} (hsymm : IsSymmetricOp D T)
    (h : IsEssentiallySelfAdjoint D T) {p q : H × H} (hp : p ∈ adjGraph D T)
    (hq : q ∈ adjGraph D T) : ⟪p.2, q.1⟫_ℂ = ⟪p.1, q.2⟫_ℂ := by
  set G : Set (H × H) := ((opGraph D T : Submodule ℂ (H × H)) : Set (H × H)) with hG
  have hpc : p ∈ closure G := by
    rw [hG, ← Submodule.topologicalClosure_coe, h.2]
    exact hp
  have hqc : q ∈ closure G := by
    rw [hG, ← Submodule.topologicalClosure_coe, h.2]
    exact hq
  have hS : IsClosed {r : (H × H) × (H × H) | ⟪r.1.2, r.2.1⟫_ℂ = ⟪r.1.1, r.2.2⟫_ℂ} :=
    isClosed_eq (Continuous.inner continuous_fst.snd continuous_snd.fst)
      (Continuous.inner continuous_fst.fst continuous_snd.snd)
  have hsub : G ×ˢ G ⊆ {r : (H × H) × (H × H) | ⟪r.1.2, r.2.1⟫_ℂ = ⟪r.1.1, r.2.2⟫_ℂ} := by
    rintro ⟨a, b⟩ ⟨⟨u, rfl⟩, ⟨v, rfl⟩⟩
    exact hsymm u v
  have hmem : ((p, q) : (H × H) × (H × H)) ∈ closure (G ×ˢ G) := by
    rw [closure_prod_eq]
    exact ⟨hpc, hqc⟩
  exact closure_minimal hsub hS hmem

/-- The linear map `(u, w) ↦ w + z • u` on `H × H`. -/
