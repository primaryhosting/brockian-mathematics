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

noncomputable def isoPlane (n : ℕ) [NeZero n] (k : ZMod n) : Submodule ℂ (ZMod n → ℂ) :=
  Submodule.span ℂ {evec n k, evec n (-k)}

