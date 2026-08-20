/-
# Singular Series Gaps 14501460
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps14501460
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

namespace Brockian

/-- A finite set `H` of integers is *admissible* (equivalently, its Hardy–Littlewood
singular series `𝔖(H)` is nonzero) when for every prime `p` the elements of `H` fail
to occupy all residue classes modulo `p`. -/

lemma admissible_of_forall_le_card {H : Finset ℕ}
    (h : ∀ p : ℕ, p.Prime → p ≤ H.card → (H.image (· % p)).card < p) :
    Admissible H := by
  intro p hp
  by_cases hle : p ≤ H.card
  · exact h p hp hle
  · exact lt_of_le_of_lt Finset.card_image_le (by omega)

