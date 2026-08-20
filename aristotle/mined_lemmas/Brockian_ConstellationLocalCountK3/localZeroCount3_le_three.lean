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

set_option grind.warning false

namespace Brockian

/-- The *local count* of a `3`-element constellation `h = (h 0, h 1, h 2)` modulo a prime `p`:
the number of residues `n : ZMod p` for which the shifted product `∏ i, (n + h i)` vanishes,
i.e. the number of residue classes that a prime constellation `(n + h 0, n + h 1, n + h 2)`
must avoid modulo `p`. -/

lemma localZeroCount3_le_three (p : ℕ) [Fact p.Prime] (h : Fin 3 → ZMod p) :
    localZeroCount3 p h ≤ 3 := by
  rw [localZeroCount3_eq_card]
  exact le_trans (Finset.card_insert_le _ _)
    (by simpa using Nat.succ_le_succ (Finset.card_insert_le (h 1) {h 2}))

/-- **Constellation local count, `k = 3`.**  For a prime `p` and a triple of shifts
`h : Fin 3 → ZMod p`:

* the number of residues killed by the constellation equals the number of distinct shifts;
* it is at most `3`;
* it is exactly `3` iff the three shifts are pairwise distinct modulo `p`;
* if `p > 3` then some residue survives, i.e. the triple is locally admissible at `p`,
  and in fact at least `p - 3` residues survive. -/
