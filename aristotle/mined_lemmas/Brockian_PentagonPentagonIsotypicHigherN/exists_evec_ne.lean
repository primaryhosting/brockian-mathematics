/-
# Pentagon Pentagon Isotypic Higher N
Category: Brockian Corpus
Target: Brockian.PentagonPentagonIsotypicHigherN
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Pentagon Pentagon Isotypic Higher N
Category: Brockian Corpus
Target: Brockian.PentagonPentagonIsotypicHigherN
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical

namespace Brockian

open DihedralGroup

noncomputable section

/-! ## The root of unity -/

/-- A primitive `n`-th root of unity in `ℂ`. -/

lemma exists_evec_ne (n : ℕ) [NeZero n] (k : ZMod n) (hk : k ≠ -k) :
    ∃ i : ZMod n, evec n k i ≠ evec n (-k) i := by
  by_contra h
  push_neg at h
  exact hk (evec_injective n (funext h))

/-- The isotypic planes are irreducible subrepresentations: every invariant subspace of
`isoPlane n k` is either trivial or all of it. -/
