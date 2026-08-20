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

/-!
# Huckel C 12
Category: Chemistry
Target: Chem.huckel_C12
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Matrix Finset

/-- The primitive 12-th root of unity `exp(2πi/12)`. -/

lemma C12_row_sum (i : ZMod 12) (f : ZMod 12 → ℂ) :
    ∑ j : ZMod 12, C12 i j * f j = f (i - 1) + f (i + 1) := by
  have hfilter : (univ.filter fun j : ZMod 12 => i - j = 1 ∨ j - i = 1) = {i - 1, i + 1} := by
    ext j
    simp only [mem_filter, mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (h | h)
      · exact Or.inl (by linear_combination -h)
      · exact Or.inr (by linear_combination h)
    · rintro (h | h)
      · exact Or.inl (by linear_combination -h)
      · exact Or.inr (by linear_combination h)
  have hne : i - 1 ≠ i + 1 := by
    intro h
    have : (2 : ZMod 12) = 0 := by linear_combination -h
    exact absurd this (by decide)
  calc ∑ j : ZMod 12, C12 i j * f j
      = ∑ j ∈ univ.filter fun j : ZMod 12 => i - j = 1 ∨ j - i = 1, f j := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases h : i - j = 1 ∨ j - i = 1 <;> simp [C12, h]
    _ = f (i - 1) + f (i + 1) := by rw [hfilter, Finset.sum_pair hne]

