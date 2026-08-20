/-
# Huckel C 17
Category: Chemistry
Target: Chem.huckel_C17
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 17
Category: Chemistry
Target: Chem.huckel_C17
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

namespace Chem

open Matrix Polynomial

/-- A primitive 17-th root of unity. -/

lemma A17_apply (i j : Fin 17) :
    A17 i j = (if j = i - 1 then 1 else 0) + (if j = i + 1 then 1 else 0) := by
  have hne : (i - 1 : Fin 17) ≠ i + 1 := by
    intro h
    rw [sub_eq_add_neg] at h
    have h2 : (-1 : Fin 17) = 1 := add_left_cancel h
    exact absurd h2 (by decide)
  have hadj : (SimpleGraph.cycleGraph 17).Adj i j ↔ (j = i - 1 ∨ j = i + 1) := by
    rw [SimpleGraph.cycleGraph_adj', fin17_val_sub_eq_one_iff, fin17_val_sub_eq_one_iff]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · right; rw [h]; abel
    · rintro (h | h)
      · exact Or.inl h
      · right; rw [h]; abel
  rw [A17, SimpleGraph.adjMatrix_apply]
  simp only [hadj]
  by_cases h1 : j = i - 1 <;> by_cases h2 : j = i + 1 <;>
    simp_all

