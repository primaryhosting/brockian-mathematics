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

lemma ngonChar_add_conj (j : ZMod n) :
    (ngonChar n j 1 : ℂ) + (ngonChar n (-j) 1 : ℂ) = ((ngonEigen n j : ℝ) : ℂ) := by
  rw [ngonChar_one, ngonChar_one]
  set x : ℝ := 2 * Real.pi * j.val / n with hx
  have h1 : (ZMod.stdAddChar j : ℂ) = Complex.exp ((x : ℂ) * Complex.I) := by
    rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply, hx]
    push_cast; ring_nf
  have h2 : (ZMod.stdAddChar (-j) : ℂ) = Complex.exp (-((x : ℂ) * Complex.I)) := by
    rw [AddChar.map_neg_eq_inv, h1, ← Complex.exp_neg]
  have h3 : ((2 * Real.cos x : ℝ) : ℂ) = 2 * Complex.cos (x : ℂ) := by
    push_cast [Complex.ofReal_cos]; ring
  rw [h1, h2, ngonEigen, ← hx, h3, Complex.two_cos]
  ring_nf

/-- The eigenvalue only depends on the pair `{j, -j}`. -/
