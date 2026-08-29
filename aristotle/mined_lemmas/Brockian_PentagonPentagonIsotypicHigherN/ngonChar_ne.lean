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

lemma ngonChar_ne (j : ZMod n) (hj : j ≠ -j) : ngonChar n j ≠ ngonChar n (-j) := by
  intro h
  apply hj
  have h1 : (ZMod.stdAddChar j : ℂ) = ZMod.stdAddChar (-j) := by
    rw [← ngonChar_one, ← ngonChar_one, h]
  exact ZMod.injective_stdAddChar h1

/-- Linear independence of the two characters spanning the isotypic component. -/
