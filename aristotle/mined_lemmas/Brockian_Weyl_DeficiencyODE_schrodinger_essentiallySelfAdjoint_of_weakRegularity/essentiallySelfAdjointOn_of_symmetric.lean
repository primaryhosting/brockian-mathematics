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
# Schrodinger Essentially Self Adjoint Of Weak Regularity
Category: Brockian (Literature Discharge)
Target: Brockian.Weyl.DeficiencyODE.schrodinger_essentiallySelfAdjoint_of_weakRegularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped InnerProductSpace ComplexConjugate ENNReal
open Filter

namespace Brockian.Weyl.DeficiencyODE

/-!
## Abstract deficiency criterion

An unbounded operator is presented here as a linear map `T` on a complex Hilbert space `H`
together with a distinguished (dense) *domain* `D`; the operator of interest is the
restriction `T|_D`.  Essential self-adjointness of a densely defined symmetric operator is
equivalent to the vanishing of both deficiency spaces `ker (T* ∓ i)`, i.e. to the density of
the ranges of `T ± i`; this is the definition used below.
-/

section Abstract

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- `T` is symmetric on the domain `D`: `⟪T x, y⟫ = ⟪x, T y⟫` for `x, y ∈ D`. -/

theorem essentiallySelfAdjointOn_of_symmetric [CompleteSpace H] (T : H →ₗ[ℂ] H)
    (hT : ∀ x y, ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ) (D : Submodule ℂ H) (hD : Dense (D : Set H)) :
    EssentiallySelfAdjointOn D T := by
  refine ⟨dense_map_add_smul_of_symmetric T hT D hD Complex.I (by simp), ?_⟩
  have h : T - Complex.I • LinearMap.id
      = T + (-Complex.I) • (LinearMap.id : H →ₗ[ℂ] H) := by
    rw [neg_smul, ← sub_eq_add_neg]
  rw [h]
  exact dense_map_add_smul_of_symmetric T hT D hD (-Complex.I) (by simp)

end Abstract

/-!
## The Schrödinger operator on `ℓ²(ℤ)`

`(Hψ) n = ψ (n + 1) + ψ (n - 1) + V n * ψ n`, the second-order difference (Weyl) operator
with potential `V`.
-/

/-- The Hilbert space `ℓ²(ℤ)`. -/
abbrev L2Z := lp (fun _ : ℤ => ℂ) 2

