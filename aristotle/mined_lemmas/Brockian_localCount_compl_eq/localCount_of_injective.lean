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

/-- The local count of a constellation (`k`-tuple of shifts) `H` modulo `p`:
the number of residues `n` mod `p` such that none of the shifted values
`n + H i` is divisible by `p`. -/

theorem localCount_of_injective {p : ℕ} [NeZero p] {k : ℕ} (H : Fin k → ZMod p)
    (hH : Function.Injective H) : localCount H = p - k := by
  have hinj : Function.Injective fun i : Fin k => -H i := fun i j hij => hH (by
    simpa using neg_injective hij)
  have hcard : (Finset.univ.image fun i : Fin k => -H i).card = k := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  rw [localCount, localCount_compl_eq, ← Finset.compl_eq_univ_sdiff, Finset.card_compl, hcard,
    ZMod.card]

/-- **Constellation local count, `k = 3`.**  For a modulus `p` and three shifts
`h₀, h₁, h₂` that are pairwise distinct modulo `p`, the number of residues `n` mod `p`
avoiding all three shifted zeros is `p - 3`. -/
