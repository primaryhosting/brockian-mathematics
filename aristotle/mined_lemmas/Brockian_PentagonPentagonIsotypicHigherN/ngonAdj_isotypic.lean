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

lemma ngonAdj_isotypic (j : ZMod n) {f : NGon n} (hf : f ∈ ngonIsotypic n j) :
    ngonAdj n f = ((ngonEigen n j : ℝ) : ℂ) • f := by
  refine ngonIsotypic_induction
    (p := fun g => ngonAdj n g = ((ngonEigen n j : ℝ) : ℂ) • g)
    (by simp) (fun a b ha hb => by beta_reduce at *; rw [map_add, ha, hb, smul_add])
    (fun c a ha => by beta_reduce at *; rw [map_smul, ha, smul_comm]) (ngonAdj_char j) ?_ hf
  beta_reduce
  rw [ngonAdj_char (-j), ngonEigen_neg]

/-- The two characters spanning the `j`-th isotypic component are distinct as soon as
`j ≠ -j`. -/
