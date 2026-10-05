import Mathlib

/-!
# Singular Series Gaps 16021610
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps16021610
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

/-- A finite set of natural numbers is *admissible* (in the sense of the
Hardy–Littlewood prime `k`-tuples conjecture: the associated singular series
is non-zero) when for every prime `p` the elements of `H` omit at least one
residue class modulo `p`. -/

theorem admissible_iff_small_primes (H : Finset ℕ) :
    Admissible H ↔ ∀ p : ℕ, p.Prime → p ≤ H.card → ∃ r < p, ∀ h ∈ H, h % p ≠ r := by
  constructor
  · intro hH p hp _
    exact hH p hp
  · intro hH p hp
    rcases le_or_gt p H.card with hle | hgt
    · exact hH p hp hle
    · exact exists_missed_residue_of_card_lt hgt

/-- The explicit `k`-element candidate tuple `{0, k!, 2·k!, …, (k-1)·k!}`. -/
