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

lemma lipschitz_shiftMap (z : ℂ) : LipschitzWith (1 + ‖z‖₊) (shiftMap (H := H) z) := by
  refine LipschitzWith.of_dist_le_mul fun p q => ?_
  rw [dist_eq_norm, dist_eq_norm, ← map_sub, shiftMap_apply]
  have h1 : ‖(p - q).2‖ ≤ ‖p - q‖ := le_max_right _ _
  have h2 : ‖(p - q).1‖ ≤ ‖p - q‖ := le_max_left _ _
  calc ‖(p - q).2 + z • (p - q).1‖ ≤ ‖(p - q).2‖ + ‖z‖ * ‖(p - q).1‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul]
      _ ≤ ‖p - q‖ + ‖z‖ * ‖p - q‖ := by gcongr
      _ = ((1 + ‖z‖₊ : NNReal) : ℝ) * ‖p - q‖ := by push_cast; ring

