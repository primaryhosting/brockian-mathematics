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

lemma zta_pow_mod (n : ℕ) [NeZero n] (a : ℕ) : (zta n) ^ (a % n) = (zta n) ^ a := by
  conv_rhs => rw [← Nat.div_add_mod a n, pow_add, pow_mul, zta_pow_n, one_pow, one_mul]

/-! ## The characters of `ZMod n` -/

/-- The `k`-th additive character of `ZMod n`, `x ↦ ζ^(k x)`. -/
