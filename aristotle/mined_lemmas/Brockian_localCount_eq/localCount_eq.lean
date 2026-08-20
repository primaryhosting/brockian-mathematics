/-
# Constellation Local Count K 3
Category: Brockian Corpus
Target: Brockian.ConstellationLocalCountK3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-- The **local count** of a constellation with shift set `H` at modulus `n`:
the number of residues `a : ZMod n` such that none of the shifted values `a + h`
(`h ∈ H`) vanishes modulo `n`.  This is the local factor appearing in the
singular series of a constellation / prime-tuple counting problem. -/

theorem localCount_eq (n : ℕ) [NeZero n] (H : Finset (ZMod n)) :
    localCount n H = n - H.card := by
  have hset : (Finset.univ.filter (fun a : ZMod n => ∀ h ∈ H, a + h ≠ 0))
      = Finset.univ \ H.image (fun h => -h) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and,
      Finset.mem_image, not_exists, not_and]
    constructor
    · intro h x hx hxa
      exact h x hx (by rw [← hxa]; exact neg_add_cancel x)
    · intro h x hx hxa
      exact h x hx (neg_eq_of_add_eq_zero_left hxa)
  have himg : (H.image (fun h => -h)).card = H.card :=
    Finset.card_image_of_injective _ neg_injective
  rw [localCount, hset, Finset.card_univ_diff, himg, ZMod.card]

/-- Local count of a one-element (`k = 1`) constellation. -/
