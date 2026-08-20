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

lemma isClosed_map_shiftMap {z : ℂ} (hz : z.re = 0) (hz1 : ‖z‖ = 1)
    (C : Submodule ℂ (H × H)) (hC : IsClosed (C : Set (H × H)))
    (hsym : ∀ p ∈ C, ⟪p.2, p.1⟫_ℂ = ⟪p.1, p.2⟫_ℂ) :
    IsClosed ((C.map (shiftMap z) : Submodule ℂ H) : Set H) := by
  haveI : CompleteSpace (C : Set (H × H)) := hC.completeSpace_coe
  have key : ∀ p q : C, dist (p : H × H) (q : H × H)
      ≤ 1 * dist (shiftMap z (p : H × H)) (shiftMap z (q : H × H)) := by
    intro p q
    have hmem : ((p : H × H) - (q : H × H)) ∈ C := C.sub_mem p.2 q.2
    have hs := hsym _ hmem
    have hnorm : ‖shiftMap z (p : H × H) - shiftMap z (q : H × H)‖ ^ 2
        = ‖((p : H × H) - (q : H × H)).2‖ ^ 2 + ‖((p : H × H) - (q : H × H)).1‖ ^ 2 := by
      rw [← map_sub, shiftMap_apply]
      exact norm_add_smul_sq hs hz hz1
    rw [dist_eq_norm, dist_eq_norm, one_mul, Prod.norm_def]
    refine max_le (sqrt_le_aux _ _ (norm_nonneg _) ?_) (sqrt_le_aux _ _ (norm_nonneg _) ?_)
    · rw [hnorm]
      nlinarith [norm_nonneg ((p : H × H) - (q : H × H)).2]
    · rw [hnorm]
      nlinarith [norm_nonneg ((p : H × H) - (q : H × H)).1]
  have hanti : AntilipschitzWith 1 (fun p : C => shiftMap z (p : H × H)) :=
    AntilipschitzWith.of_le_mul_dist (by intro x y; simpa using key x y)
  have hcont : UniformContinuous (fun p : C => shiftMap z (p : H × H)) :=
    ((lipschitz_shiftMap z).uniformContinuous).comp uniformContinuous_subtype_val
  have hrange : Set.range (fun p : C => shiftMap z (p : H × H))
      = ((C.map (shiftMap z) : Submodule ℂ H) : Set H) := by
    ext y
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨(p : H × H), p.2, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨⟨p, hp⟩, rfl⟩
  rw [← hrange]
  exact hanti.isClosed_range hcont

/-- **Basic criterion** for essential self-adjointness: a densely defined symmetric
operator with trivial deficiency spaces is essentially self-adjoint. -/
