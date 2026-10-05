import Mathlib

/-!
# Pentagon Pentagon Isotypic Higher N
Category: Brockian Corpus
Target: Brockian.PentagonPentagonIsotypicHigherN
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean 4 requires every `import` to precede any module docstring, so the header
-- comment above sits immediately after the single `import Mathlib` line.

open scoped BigOperators
open scoped Real
open scoped Classical

set_option maxHeartbeats 1000000

namespace Brockian

/-- The vertex space of the regular `n`-gon: complex-valued functions on the vertex
set `ZMod n`.  The dihedral group `D_n` acts on it through the rotation `ngonShift`
and the reflection `ngonRefl`. -/
abbrev NGon (n : ℕ) : Type := ZMod n → ℂ

/-- Rotation of the `n`-gon by `t` vertices, acting on functions by translation. -/

lemma ngonEigen_neg (j : ZMod n) : ngonEigen n (-j) = ngonEigen n j := by
  have h := ngonChar_add_conj (n := n) (-j)
  rw [neg_neg, add_comm] at h
  have := (ngonChar_add_conj (n := n) j).symm.trans h
  exact_mod_cast this.symm

/-- Each character is an eigenvector of the adjacency operator, with eigenvalue
`2 cos (2π j / n)`. -/
