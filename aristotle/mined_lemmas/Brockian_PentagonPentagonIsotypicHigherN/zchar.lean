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

noncomputable def zchar (n : ℕ) [NeZero n] (k : ZMod n) : AddChar (ZMod n) ℂ :=
  AddChar.zmodChar n (ζ := zta n ^ k.val)
    (by rw [← pow_mul, mul_comm, pow_mul, zta_pow_n, one_pow])

