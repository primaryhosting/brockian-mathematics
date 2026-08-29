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

lemma ngonRep_sr_evec (n : ℕ) [NeZero n] (i k : ZMod n) :
    ngonRep n (sr i) (evec n k) = (evec n k i) • evec n (-k) := by
  funext x
  rw [ngonRep_sr, evec_sub_arg, Pi.smul_apply, smul_eq_mul]

/-! ## The isotypic planes -/

/-- The `k`-th isotypic plane: the span of the `k`-th and `(-k)`-th isotypic vectors. -/
