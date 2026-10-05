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

lemma ngonAdj_char (j : ZMod n) :
    ngonAdj n ⇑(ngonChar n j) = ((ngonEigen n j : ℝ) : ℂ) • ⇑(ngonChar n j) := by
  have hneg : (ngonChar n j (-1) : ℂ) = ngonChar n (-j) 1 := by
    simp [ngonChar_apply]
  rw [ngonAdj, LinearMap.add_apply, ngonShift_char, ngonShift_char, hneg,
    ← add_smul, ngonChar_add_conj]

/-- Membership in the isotypic component can be checked on the two generating
characters. -/
