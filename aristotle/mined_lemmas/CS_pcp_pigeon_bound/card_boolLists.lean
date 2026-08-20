/-
# Pcp Pigeon Bound
Category: Computer Science
Target: CS.pcp_pigeon_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace CS

/-- The finite set of all boolean lists of a given length. -/

lemma card_boolLists (k : ℕ) : (boolLists k).card = 2 ^ k := by
  have h : (Finset.univ : Finset (List.Vector Bool k)).card = 2 ^ k := by
    rw [Finset.card_univ, card_vector]; simp
  rw [boolLists, Finset.card_image_of_injective _ Subtype.val_injective, h]

/-- The set of length-`n` extensions of a word `w`. -/
