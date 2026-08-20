import Mathlib

/-!
# Singular Series Gaps 12401250
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps12401250
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

/-- A finite set of shifts `H` is *admissible* (in the sense of the Hardy–Littlewood
prime `k`-tuple conjecture) if for every prime `p` the residues of `H` modulo `p`
do not cover all of `ℤ/pℤ`.  Equivalently, the local factor of the singular series
attached to `H` is nonzero at every prime. -/

theorem admissible_iff_small_primes (H : Finset ℕ) :
    Admissible H ↔ ∀ p : ℕ, p.Prime → p ≤ H.card → (H.image (· % p)).card < p := by
  constructor
  · intro h p hp _
    exact h p hp
  · intro h p hp
    by_cases hle : p ≤ H.card
    · exact h p hp hle
    · exact lt_of_le_of_lt (Finset.card_image_le) (by omega)

/-- The two–element pattern `{0, g}` is admissible exactly when the gap `g`
is even.  (For odd `g` one of `0, g` is even and the other odd, so the pattern covers
both residue classes mod `2`.) -/
