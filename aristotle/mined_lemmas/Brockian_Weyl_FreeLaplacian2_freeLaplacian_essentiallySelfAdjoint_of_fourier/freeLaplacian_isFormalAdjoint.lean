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
# A basic criterion for essential self-adjointness

Let `T` be a densely defined symmetric operator on a complex Hilbert space `H`.
If the ranges of `T + i` and `T - i` are both dense, then the adjoint `T†` is
self-adjoint, i.e. `T` is essentially self-adjoint.

Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped ComplexConjugate
open LinearPMap MeasureTheory Filter Topology

namespace Brockian.Weyl

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local notation "⟪" x ", " y "⟫" => inner ℂ x y

/-- The range of `T + z` for a partially defined operator `T` and a scalar `z`. -/

theorem freeLaplacian_isFormalAdjoint : freeLaplacian.IsFormalAdjoint freeLaplacian := by
  intro x y
  obtain ⟨u, hu⟩ := x.2
  obtain ⟨v, hv⟩ := y.2
  have hx : x = ⟨schwartzToL2 u, mem_freeLaplacian_domain u⟩ := Subtype.ext hu.symm
  have hy : y = ⟨schwartzToL2 v, mem_freeLaplacian_domain v⟩ := Subtype.ext hv.symm
  subst hx
  subst hy
  rw [freeLaplacian_apply, freeLaplacian_apply]
  show inner ℂ (schwartzToL2 (freeLaplacianSchwartz u)) (schwartzToL2 v)
    = inner ℂ (schwartzToL2 u) (schwartzToL2 (freeLaplacianSchwartz v))
  simp only [schwartzToL2_apply, SchwartzMap.inner_toL2_toL2_eq, freeLaplacianSchwartz_apply]
  have hdu : ⇑(SchwartzMap.derivCLM ℂ ℂ u) = deriv ⇑u := by
    ext x; simp [SchwartzMap.derivCLM_apply]
  have hdv : ⇑(SchwartzMap.derivCLM ℂ ℂ v) = deriv ⇑v := by
    ext x; simp [SchwartzMap.derivCLM_apply]
  have key := integral_conj_deriv_two u v
  simp only [RCLike.inner_apply, SchwartzMap.neg_apply, SchwartzMap.derivCLM_apply, hdu, hdv,
    map_neg, neg_mul, mul_neg, integral_neg, key]

/-- The range of `freeLaplacian + z` is dense for non-real `z`. -/
