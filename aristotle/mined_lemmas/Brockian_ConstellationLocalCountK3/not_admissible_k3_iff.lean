/-!
# Constellation Local Count K 3
Category: Brockian Corpus
Target: Brockian.ConstellationLocalCountK3
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian

/-- The *local count* `ν_p(H)` of a finite tuple `H` of integers at a modulus `p`:
the number of distinct residue classes modulo `p` occupied by the members of `H`. -/

theorem not_admissible_k3_iff (H : Finset ℤ) (hH : H.card = 3) :
    ¬ Admissible H ↔ (localCount 2 H = 2 ∨ localCount 3 H = 3) := by
  have hb2 : localCount 2 H ≤ 2 := by
    have := localCount_le_card 2 H
    have h2 : localCount 2 H ≤ Fintype.card (ZMod 2) :=
      Finset.card_le_univ _
    simpa using h2
  have hb3 : localCount 3 H ≤ 3 := by
    have := localCount_le_card 3 H
    omega
  rw [ConstellationLocalCountK3 H hH]
  omega

/-- The triple `{0, 2, 6}` is an admissible constellation. -/
