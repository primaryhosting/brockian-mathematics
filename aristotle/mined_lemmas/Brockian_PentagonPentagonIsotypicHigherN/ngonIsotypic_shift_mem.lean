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

lemma ngonIsotypic_shift_mem (j t : ZMod n) {f : NGon n} (hf : f ∈ ngonIsotypic n j) :
    ngonShift n t f ∈ ngonIsotypic n j := by
  refine ngonIsotypic_induction (p := fun g => ngonShift n t g ∈ ngonIsotypic n j)
    (by simp) (fun a b ha hb => by beta_reduce at *; rw [map_add]; exact Submodule.add_mem _ ha hb)
    (fun c a ha => by beta_reduce at *; rw [map_smul]; exact Submodule.smul_mem _ _ ha) ?_ ?_ hf
  · beta_reduce
    rw [ngonShift_char]
    exact Submodule.smul_mem _ _ (ngonChar_mem_isotypic j)
  · beta_reduce
    rw [ngonShift_char]
    exact Submodule.smul_mem _ _ (ngonChar_neg_mem_isotypic j)

/-- The isotypic component is invariant under the reflection. -/
