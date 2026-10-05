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

lemma ngonIsotypic_finrank (j : ZMod n) (hj : j ≠ -j) :
    Module.finrank ℂ (ngonIsotypic n j) = 2 := by
  have hrange : Set.range ![⇑(ngonChar n j), ⇑(ngonChar n (-j))]
      = {⇑(ngonChar n j), ⇑(ngonChar n (-j))} := by
    simp [Matrix.range_cons, Matrix.range_empty, Set.pair_comm]
  rw [ngonIsotypic, ← hrange]
  simpa using finrank_span_eq_card (ngonChar_linearIndependent j hj)

end Lemmas

section Pentagon

/-- The classical pentagon eigenvalue `2 cos (2π/5) = (√5 - 1)/2`. -/
