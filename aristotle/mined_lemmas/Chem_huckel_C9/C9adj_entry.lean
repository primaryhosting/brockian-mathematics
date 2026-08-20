import Mathlib

/-!
# Huckel C 9
Category: Chemistry
Target: Chem.huckel_C9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean 4 requires `import` lines to precede all other commands, including module
docstrings, so the required header comment appears immediately after the import.)
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

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Chem

open Matrix Polynomial

/-- The adjacency matrix of the cycle graph `C₉`, with vertices indexed by `ZMod 9`:
vertices `i` and `j` are adjacent iff they differ by `1` modulo `9`. -/

lemma C9adj_entry (i j : ZMod 9) :
    (C9adj i j : ℂ) = (if j = i - 1 then 1 else 0) + (if j = i + 1 then 1 else 0) := by
  have e1 : (i - j = 1) ↔ (j = i - 1) := by
    constructor <;> intro h <;> linear_combination -h
  have e2 : (j - i = 1) ↔ (j = i + 1) := by
    constructor <;> intro h <;> linear_combination h
  have hne : (i - 1 : ZMod 9) ≠ i + 1 := by
    intro h
    exact absurd (show (2 : ZMod 9) = 0 by linear_combination -h) (by decide)
  simp only [C9adj, Matrix.of_apply, e1, e2]
  by_cases h1 : j = i - 1
  · simp [h1, hne]
  · by_cases h2 : j = i + 1
    · simp [h2, Ne.symm hne]
    · simp [h1, h2]

