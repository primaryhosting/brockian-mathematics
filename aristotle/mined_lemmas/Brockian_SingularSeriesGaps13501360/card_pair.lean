/-
# Singular Series Gaps 13501360
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps13501360
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian

/-- The number of distinct residue classes modulo `p` occupied by the tuple `H`.
This is the local density `ν_p(H)` appearing in the Hardy–Littlewood singular series. -/

lemma card_pair {d : ℤ} (hd : d ≠ 0) : ({0, d} : Finset ℤ).card = 2 := by
  rw [Finset.card_insert_of_notMem (by simpa using hd.symm), Finset.card_singleton]

/-- If `p` divides `d` then the pair `{0, d}` occupies a single class mod `p`. -/
