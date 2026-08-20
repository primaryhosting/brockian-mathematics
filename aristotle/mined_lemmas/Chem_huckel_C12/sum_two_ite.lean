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

open scoped BigOperators Real
open Polynomial Matrix

namespace Chem

/-- A primitive 12-th root of unity. -/

lemma sum_two_ite (a b : Fin 12) (hab : a ≠ b) (f : Fin 12 → ℂ) :
    ∑ j, (if j = a ∨ j = b then (1 : ℂ) else 0) * f j = f a + f b := by
  have key : ∀ j : Fin 12, (if j = a ∨ j = b then (1 : ℂ) else 0) * f j
      = (if j = a then f j else 0) + (if j = b then f j else 0) := by
    intro j
    by_cases h1 : j = a <;> by_cases h2 : j = b <;> simp_all
  rw [Finset.sum_congr rfl (fun j _ => key j), Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ a f, Finset.sum_ite_eq' Finset.univ b f]
  simp

/-- The columns of the DFT matrix are eigenvectors of the adjacency matrix. -/
