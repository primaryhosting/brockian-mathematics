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

theorem ConstellationLocalCountK1 (n : ℕ) [NeZero n] (h₁ : ZMod n) :
    localCount n {h₁} = n - 1 := by
  rw [localCount_eq, Finset.card_singleton]

/-- Local count of a two-element (`k = 2`) constellation with distinct shifts. -/
