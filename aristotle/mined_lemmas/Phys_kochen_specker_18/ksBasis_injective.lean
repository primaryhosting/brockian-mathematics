import Mathlib

/-!
# Kochen Specker 18
Category: Frontier Phys
Target: Phys.kochen_specker_18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace Phys

/-- The 18 vectors of the Cabello–Estebaranz–García-Alcaine Kochen–Specker set in `ℝ⁴`. -/

theorem ksBasis_injective (b : Fin 9) (i j : Fin 4) (h : ksBasis b i = ksBasis b j) : i = j := by
  fin_cases b <;> fin_cases i <;> fin_cases j <;> simp_all [ksBasis]

/-- **Kochen–Specker theorem (18-vector version).**
The explicit 18 vectors `ksVec` in `ℝ⁴` form nine orthogonal bases (the four vectors of each
quadruple `ksBasis b` are pairwise orthogonal and nonzero), yet there is no `{0,1}`-coloring
of the 18 vectors assigning the value `1` to exactly one vector of each basis. -/
