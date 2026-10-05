import Mathlib

/-!
# Constellation Local Count K 3
Category: Brockian Corpus
Target: Brockian.ConstellationLocalCountK3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian

/-- The local count, modulo `p`, of a constellation with offset set `A`:
the number of residues `n : ZMod p` such that none of the shifted values `n + a`
(for `a ∈ A`) is divisible by `p`. -/

theorem localCount_eq (p : ℕ) [NeZero p] (A : Finset (ZMod p)) :
    localCount p A = p - A.card := by
  have hinj : Function.Injective (fun a : ZMod p => -a) := neg_injective
  rw [localCount, localCount_filter_eq, Finset.card_compl,
    Finset.card_image_of_injective _ hinj, ZMod.card]

/-- **Constellation local count, `k = 3`.**  For a constellation given by three offsets
`a b c : ZMod p` that are pairwise distinct modulo `p`, the number of residues `n mod p`
avoiding all three forbidden classes is exactly `p - 3`. -/
