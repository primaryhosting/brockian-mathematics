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

theorem ksBasis_orthogonal (b : Fin 9) (i j : Fin 4) (hij : i ≠ j) :
    ksDot (ksVec (ksBasis b i)) (ksVec (ksBasis b j)) = 0 := by
  fin_cases b <;> fin_cases i <;> fin_cases j <;>
    simp [ksDot, ksVec, ksBasis, Fin.sum_univ_four] at hij ⊢

/-- The four indices in each quadruple are distinct. -/
