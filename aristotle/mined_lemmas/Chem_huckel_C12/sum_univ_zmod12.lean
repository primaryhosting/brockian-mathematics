import Mathlib

/-!
# Huckel C 12
Category: Chemistry
Target: Chem.huckel_C12
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real

set_option maxHeartbeats 1000000

namespace Chem

open Complex Polynomial Matrix Finset

/-- The primitive 12-th root of unity `exp(2πi/12)`. -/

lemma sum_univ_zmod12 (f : ZMod 12 → ℂ) :
    ∑ k : ZMod 12, f k = ∑ n ∈ Finset.range 12, f (n : ZMod 12) := by
  refine (Finset.sum_nbij' (fun n => ((n : ℕ) : ZMod 12)) (fun k => k.val) ?_ ?_ ?_ ?_ ?_)
  · intro n _; exact Finset.mem_univ _
  · intro k _; exact Finset.mem_range.mpr (ZMod.val_lt k)
  · intro n hn; simpa using ZMod.val_natCast_of_lt (Finset.mem_range.mp hn)
  · intro k _; exact ZMod.natCast_zmod_val k
  · intro n _; rfl

/-- Orthogonality of characters: the sum of `ζ^{km}` over `k` vanishes unless `m = 0`. -/
