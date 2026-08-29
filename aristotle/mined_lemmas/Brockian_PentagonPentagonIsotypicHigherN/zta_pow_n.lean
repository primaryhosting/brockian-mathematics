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

lemma zta_pow_n (n : ℕ) [NeZero n] : (zta n) ^ n = 1 := (zta_prim n).pow_eq_one

