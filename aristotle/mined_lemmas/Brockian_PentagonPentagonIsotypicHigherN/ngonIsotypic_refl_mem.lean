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

lemma ngonIsotypic_refl_mem (j : ZMod n) {f : NGon n} (hf : f ∈ ngonIsotypic n j) :
    ngonRefl n f ∈ ngonIsotypic n j := by
  refine ngonIsotypic_induction (p := fun g => ngonRefl n g ∈ ngonIsotypic n j)
    (by simp) (fun a b ha hb => by beta_reduce at *; rw [map_add]; exact Submodule.add_mem _ ha hb)
    (fun c a ha => by beta_reduce at *; rw [map_smul]; exact Submodule.smul_mem _ _ ha) ?_ ?_ hf
  · beta_reduce
    rw [ngonRefl_char]
    exact ngonChar_neg_mem_isotypic j
  · beta_reduce
    rw [ngonRefl_char, neg_neg]
    exact ngonChar_mem_isotypic j

/-- The adjacency operator acts on the whole `j`-th isotypic component as the scalar
`2 cos (2π j / n)`. -/
