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

theorem finrank_isoPlane_of_eq (n : ℕ) [NeZero n] (k : ZMod n) (hk : k = -k) :
    Module.finrank ℂ (isoPlane n k) = 1 := by
  have : ({evec n k, evec n (-k)} : Set (ZMod n → ℂ)) = {evec n k} := by
    rw [← hk]; simp
  rw [isoPlane, this]
  exact finrank_span_singleton (evec_ne_zero n k)

/-! ## Irreducibility of the isotypic planes -/

