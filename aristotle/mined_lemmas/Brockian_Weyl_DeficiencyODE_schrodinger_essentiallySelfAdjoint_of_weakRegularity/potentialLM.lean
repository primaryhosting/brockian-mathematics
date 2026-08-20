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

noncomputable def potentialLM (V : ℤ → ℝ) (hV : ∃ C, ∀ n, |V n| ≤ C) : L2Z →ₗ[ℂ] L2Z where
  toFun ψ := ⟨fun n => (V n : ℂ) * ψ n, memℓp_mul_bounded hV.choose_spec (lp.memℓp ψ)⟩
  map_add' := by intro f g; ext n; simp [mul_add]
  map_smul' := by intro c f; ext n; simp; ring

/-- The Schrödinger operator `(Hψ) n = ψ (n+1) + ψ (n-1) + V n * ψ n` on `ℓ²(ℤ)`. -/
