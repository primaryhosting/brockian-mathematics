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

namespace Chem

open Complex Matrix

/-- A primitive 12-th root of unity. -/

lemma sum_C12_pow (i : Fin 12) (u : ℂ) (hu : u ^ 12 = 1) :
    ∑ j : Fin 12, C12 i j * u ^ (j : ℕ) = u ^ (i : ℕ) * (u + u ^ 11) := by
  fin_cases i <;>
    simp [C12, Fin.sum_univ_succ] <;>
    first
      | ring1
      | linear_combination (-1 : ℂ) * hu
      | linear_combination (-u) * hu
      | linear_combination (-u ^ 2) * hu
      | linear_combination (-u ^ 3) * hu
      | linear_combination (-u ^ 4) * hu
      | linear_combination (-u ^ 5) * hu
      | linear_combination (-u ^ 6) * hu
      | linear_combination (-u ^ 7) * hu
      | linear_combination (-u ^ 8) * hu
      | linear_combination (-u ^ 9) * hu
      | linear_combination (-(1 + u ^ 10)) * hu

