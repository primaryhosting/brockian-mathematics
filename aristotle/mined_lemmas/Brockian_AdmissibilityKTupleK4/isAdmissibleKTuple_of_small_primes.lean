import Mathlib

/-!
# Admissibility Ktuple K 4
Category: Brockian Corpus
Target: Brockian.AdmissibilityKTupleK4
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

/-- A `k`-tuple `H : Fin k → ℕ` is *admissible* when, for every prime `p`, the values
`H i` do not cover all residue classes modulo `p`. -/

theorem isAdmissibleKTuple_of_small_primes {k : ℕ} (H : Fin k → ℕ)
    (h : ∀ p : ℕ, p.Prime → p ≤ k → ∃ r : ZMod p, ∀ i : Fin k, (H i : ZMod p) ≠ r) :
    IsAdmissibleKTuple k H := by
  intro p hp
  rcases le_or_gt p k with hpk | hpk
  · exact h p hp hpk
  · haveI : Fact p.Prime := ⟨hp⟩
    haveI : NeZero p := ⟨hp.ne_zero⟩
    exact exists_missing_residue_of_card_lt H p hpk

/-- **Admissibility for 4-tuples.** The prime 4-tuple pattern `(0, 2, 6, 8)` is admissible:
for every prime `p` the four shifts omit at least one residue class modulo `p`. -/
