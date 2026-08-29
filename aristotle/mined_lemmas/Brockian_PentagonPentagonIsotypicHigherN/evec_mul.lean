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

lemma evec_mul (n : ℕ) [NeZero n] (j k : ZMod n) :
    evec n j * evec n k = evec n (j + k) := by
  funext x
  simp only [Pi.mul_apply, evec_apply, ← pow_add, add_mul]
  rw [ZMod.val_add, zta_pow_mod]

/-! ## The vertex representation of the dihedral group -/

/-- The action of the dihedral group on functions on the vertices of the `n`-gon. -/
