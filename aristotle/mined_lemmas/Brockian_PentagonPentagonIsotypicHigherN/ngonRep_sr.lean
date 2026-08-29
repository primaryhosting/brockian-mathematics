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

@[simp] lemma ngonRep_sr (n : ℕ) (i : ZMod n) (f : ZMod n → ℂ) (x : ZMod n) :
    ngonRep n (sr i) f x = f (i - x) := rfl

/-- Rotations act on isotypic vectors by a scalar. -/
