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

noncomputable def localZeroCount3 (p : ℕ) [Fact p.Prime] (h : Fin 3 → ZMod p) : ℕ :=
  (Finset.univ.filter (fun n : ZMod p => ∏ i, (n + h i) = 0)).card

/-- The set of "bad" residues is exactly the set of negatives of the shifts. -/
