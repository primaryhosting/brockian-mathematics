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

lemma sum_indicator_left (i : ZMod 12) (u : ZMod 12 → ℂ) :
    ∑ j : ZMod 12, (if j = i + 1 ∨ j = i - 1 then (1 : ℂ) else 0) * u j
      = u (i + 1) + u (i - 1) := by
  have h1 : ∀ j : ZMod 12, (if j = i + 1 ∨ j = i - 1 then (1 : ℂ) else 0) * u j
      = if j = i + 1 ∨ j = i - 1 then u j else 0 := by
    intro j; split <;> simp
  rw [Finset.sum_congr rfl (fun j _ => h1 j), ← Finset.sum_filter]
  have h2 : Finset.univ.filter (fun j : ZMod 12 => j = i + 1 ∨ j = i - 1) = {i + 1, i - 1} := by
    ext j; simp
  rw [h2, Finset.sum_pair (ne_add_one_sub_one i)]

