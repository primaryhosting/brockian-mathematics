import Mathlib

/-!
# Singular Series Gaps 13501360
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps13501360
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

/-- The set of residue classes modulo `p` occupied by the tuple `H`. -/

lemma card_gapTuple_le (a d k : ℕ) : (gapTuple a d k).card ≤ k := by
  simpa [gapTuple] using
    (Finset.card_image_le (s := Finset.range k) (f := fun i => a + i * d)).trans_eq
      (Finset.card_range k)

/-- If `p ∣ d` then every element of the progression lies in the single class `a mod p`. -/
