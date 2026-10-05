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

lemma evec_sub_arg (n : ℕ) [NeZero n] (k x y : ZMod n) :
    evec n k (x - y) = evec n k x * evec n (-k) y := by
  rw [sub_eq_add_neg, evec_add_arg, evec_neg_arg]

/-- Pointwise multiplication of isotypic vectors adds the isotypic labels. -/
