import Mathlib

/-!
# Huckel C 10
Category: Chemistry
Target: Chem.huckel_C10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real

open Matrix Polynomial

namespace Chem

/-! ## A primitive tenth root of unity and the associated additive character -/

/-- A primitive `10`-th root of unity. -/

theorem C10_charpoly :
    C10.charpoly = ∏ k : ZMod 10, (X - C (huckelEigenvalue k)) := by
  rw [C10_eq_conj, Matrix.charpoly_units_conj, Matrix.charpoly_diagonal]

