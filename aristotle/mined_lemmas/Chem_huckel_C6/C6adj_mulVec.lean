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
# Huckel C 6
Category: Chemistry
Target: Chem.huckel_C6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 6
Category: Chemistry
Target: Chem.huckel_C6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Real

namespace Chem

/-- A primitive sixth root of unity. -/

lemma C6adj_mulVec (v : Fin 6 → ℂ) (x : Fin 6) :
    C6adj.mulVec v x = v (x + 1) + v (x - 1) := by
  have hne : x + 1 ≠ x - 1 := by
    intro h
    rw [sub_eq_add_neg] at h
    exact absurd (add_left_cancel h : (1 : Fin 6) = -1) (by decide)
  have key : ∀ j : Fin 6, (if j = x + 1 ∨ j = x - 1 then (1 : ℂ) else 0) * v j
      = (if j = x + 1 then v j else 0) + (if j = x - 1 then v j else 0) := by
    intro j
    by_cases h1 : j = x + 1 <;> by_cases h2 : j = x - 1 <;> simp_all
  simp only [C6adj, Matrix.mulVec, dotProduct, Matrix.of_apply, key, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- The Fourier vector `x ↦ ω ^ (k x)` is an eigenvector of the adjacency matrix
of `C₆` with eigenvalue `2 cos (2πk/6)`. -/
