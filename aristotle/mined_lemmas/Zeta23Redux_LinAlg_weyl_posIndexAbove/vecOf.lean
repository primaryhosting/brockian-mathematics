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

open Matrix Finset

namespace Zeta23Redux.LinAlg

variable {d : ℕ}

/-- The number of strictly positive eigenvalues of a Hermitian matrix. -/

noncomputable def vecOf (b : OrthonormalBasis (Fin d) ℂ (EuclideanSpace ℂ (Fin d)))
    (S : Finset (Fin d)) : (S → ℂ) →ₗ[ℂ] EuclideanSpace ℂ (Fin d) where
  toFun c := b.repr.symm (WithLp.toLp 2 (fun k => if h : k ∈ S then c ⟨k, h⟩ else 0))
  map_add' c c' := by
    simp only [← map_add]
    congr 1
    ext k
    by_cases h : k ∈ S <;> simp [h]
  map_smul' a c := by
    simp only [← map_smul]
    congr 1
    ext k
    by_cases h : k ∈ S <;> simp [h]

