/-
# Pcp Pigeon Bound
Category: Computer Science
Target: CS.pcp_pigeon_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace CS

open Finset

/-- The finite set of all binary strings of length `n`. -/

lemma card_binWords (n : ℕ) : (binWords n).card = 2 ^ n := by
  rw [binWords, Finset.card_image_of_injective _ List.ofFn_injective]
  simp

/-- A finite set of binary strings is *prefix-free* if no member is a prefix of a
different member. -/
