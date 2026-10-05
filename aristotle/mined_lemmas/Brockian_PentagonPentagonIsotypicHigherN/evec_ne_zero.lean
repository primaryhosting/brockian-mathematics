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

lemma evec_ne_zero (n : ℕ) [NeZero n] (k : ZMod n) : evec n k ≠ 0 := by
  intro h
  have h0 : evec n k 0 = 0 := by rw [h]; rfl
  rw [evec_apply] at h0
  simp only [mul_zero, ZMod.val_zero, pow_zero] at h0
  exact one_ne_zero h0

