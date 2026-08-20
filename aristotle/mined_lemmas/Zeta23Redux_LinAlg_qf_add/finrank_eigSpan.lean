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
# Weyl Pos Index Above
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.weyl_posIndexAbove
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Zeta23Redux.LinAlg

open Matrix Finset Module

variable {d : ℕ}

/-- The quadratic form `x ↦ Re ⟪x, M x⟫` associated with a matrix `M`, on `EuclideanSpace ℂ (Fin d)`.
-/

lemma finrank_eigSpan (hM : M.IsHermitian) (s : Finset (Fin d)) :
    finrank ℂ (eigSpan hM s) = s.card := by
  have hli : LinearIndependent ℂ (fun j : {x // x ∈ s} => hM.eigenvectorBasis j) :=
    hM.eigenvectorBasis.orthonormal.linearIndependent.comp _ Subtype.val_injective
  rw [eigSpan, finrank_span_eq_card hli, Fintype.card_coe]

