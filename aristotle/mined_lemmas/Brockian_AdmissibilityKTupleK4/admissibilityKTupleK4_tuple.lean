/-
# Admissibility Ktuple K 4
Category: Brockian Corpus
Target: Brockian.AdmissibilityKTupleK4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Admissibility Ktuple K 4
Category: Brockian Corpus
Target: Brockian.AdmissibilityKTupleK4
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

namespace Brockian

/-- A finite set of integers `H` (thought of as a tuple of shifts `h₁ < ⋯ < h_k`) is
*admissible* if for every prime `p` the elements of `H` do not cover all residue classes
modulo `p`; equivalently, some residue class mod `p` is missed by `H`.  This is the
classical admissibility condition from the Hardy–Littlewood prime `k`-tuple conjecture. -/

theorem admissibilityKTupleK4_tuple (h : Fin 4 → ℤ) (hinj : Function.Injective h) :
    Admissible (Finset.image h Finset.univ) ↔
      ((∃ a : ZMod 2, ∀ i : Fin 4, (h i : ZMod 2) ≠ a) ∧
        (∃ a : ZMod 3, ∀ i : Fin 4, (h i : ZMod 3) ≠ a)) := by
  have hcard : (Finset.image h Finset.univ).card = 4 := by
    rw [Finset.card_image_of_injective _ hinj]
    simp
  rw [AdmissibilityKTupleK4 _ hcard]
  simp

/-- The `4`-tuple `(0, 1, 2, 3)` is *not* admissible: it covers both residue classes mod `2`. -/
