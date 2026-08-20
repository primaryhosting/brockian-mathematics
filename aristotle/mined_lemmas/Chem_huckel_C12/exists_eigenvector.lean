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
# Huckel C 12
Category: Chemistry
Target: Chem.huckel_C12
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real

namespace Chem

open Complex Matrix Finset

/-- The primitive 12-th root of unity `exp(2πi/12)`. -/

lemma exists_eigenvector (k : ZMod 12) :
    ∃ v : ZMod 12 → ℂ, v ≠ 0 ∧ C12adj *ᵥ v = lam k • v := by
  refine ⟨fun j => xi (j * k), ?_, ?_⟩
  · intro h
    have h0 : xi ((0 : ZMod 12) * k) = 0 := congrFun h 0
    exact xi_ne_zero _ h0
  · funext i
    show ∑ j : ZMod 12, C12adj i j * xi (j * k) = lam k * xi (i * k)
    have h : ∀ j : ZMod 12, C12adj i j * xi (j * k)
        = (if j = i + 1 ∨ j = i - 1 then (1 : ℂ) else 0) * (fun j : ZMod 12 => xi (j * k)) j :=
      fun j => rfl
    rw [Finset.sum_congr rfl (fun j _ => h j), sum_indicator_left]
    have e1 : xi ((i + 1) * k) = xi (i * k) * xi k := by rw [← xi_add]; congr 1; ring
    have e2 : xi ((i - 1) * k) = xi (i * k) * xi (-k) := by rw [← xi_add]; congr 1; ring
    rw [e1, e2, ← lam_eq k]
    ring

/-- Every eigenvalue of the adjacency matrix is one of the `2 cos(2πk/12)`. -/
