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

lemma C8adj_eq_map : C8adj = ((Int.castRingHom ℂ).mapMatrix C8adjInt) := by
  ext i j
  simp only [C8adj, C8adjInt, RingHom.mapMatrix_apply, Matrix.map_apply, eq_intCast]
  split <;> simp

/-- The adjacency matrix of `C₈` satisfies `A⁵ = 6A³ - 8A`, i.e. it is annihilated by
the polynomial `x(x² - 2)(x² - 4)`. -/
