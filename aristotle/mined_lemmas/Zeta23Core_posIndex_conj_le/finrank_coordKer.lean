import Mathlib

/-!
# Pos Index Conj Le
Category: Brockian Corpus
Target: Zeta23Core.posIndex_conj_le
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Zeta23Core

open Matrix Module

variable {𝕜 : Type*} [RCLike 𝕜] {m d : Type*} [Fintype m] [DecidableEq m] [Fintype d]
  [DecidableEq d]

/-- The real quadratic form `x ↦ xᴴ Q x` attached to a matrix `Q`. -/

lemma finrank_coordKer (p : m → Prop) :
    finrank 𝕜 (coordKer p : Submodule 𝕜 (m → 𝕜)) = Fintype.card m - Fintype.card {i // p i} := by
  have hsurj : Function.Surjective (LinearMap.funLeft 𝕜 𝕜 (Subtype.val : {i // p i} → m)) :=
    LinearMap.funLeft_surjective_of_injective _ _ _ Subtype.val_injective
  have h := LinearMap.finrank_range_add_finrank_ker
    (LinearMap.funLeft 𝕜 𝕜 (Subtype.val : {i // p i} → m))
  rw [LinearMap.range_eq_top.2 hsurj] at h
  simp only [finrank_top, Module.finrank_pi] at h
  simp only [coordKer]
  omega

/-- The quadratic form of a real diagonal matrix. -/
