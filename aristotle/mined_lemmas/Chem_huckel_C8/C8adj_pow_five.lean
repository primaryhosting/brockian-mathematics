/-
# Huckel C 8
Category: Chemistry
Target: Chem.huckel_C8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Huckel C 8
Category: Chemistry
Target: Chem.huckel_C8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

/-- The adjacency matrix of the cycle graph `C₈`, indexed by `ZMod 8`
(vertex `i` is adjacent to `i + 1` and `i - 1`), with complex entries. -/

lemma C8adj_pow_five : C8adj ^ 5 = 6 * C8adj ^ 3 - 8 * C8adj := by
  have h : C8adjInt ^ 5 = 6 * C8adjInt ^ 3 - 8 * C8adjInt := by decide
  rw [C8adj_eq_map, ← map_pow, ← map_pow, h, map_sub, map_mul, map_mul, map_ofNat, map_ofNat]

