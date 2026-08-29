/-
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The Hückel model for the annulene `C₁₈` uses the adjacency matrix of the cycle
graph `C₁₈`.  We show that its eigenvalues are exactly the `18` numbers
`2 cos (2πk/18)`, `k = 0, …, 17`.
-/

namespace Chem

open Complex Matrix

/-- The adjacency matrix of the cycle graph `C₁₈` on the vertex set `Fin 18`:
vertices `i` and `j` are adjacent iff they are consecutive modulo `18`. -/

lemma key (z : ℂ) (hz : z ^ 18 = 1) (i : Fin 18) :
    ∑ j : Fin 18, C18adj i j * z ^ j.val = (z + z ^ 17) * z ^ i.val := by
  fin_cases i <;>
    simp [C18adj, Fin.sum_univ_succ] <;>
    first
      | ring1
      | linear_combination -hz
      | linear_combination -z * hz
      | linear_combination -z ^ 2 * hz
      | linear_combination -z ^ 3 * hz
      | linear_combination -z ^ 4 * hz
      | linear_combination -z ^ 5 * hz
      | linear_combination -z ^ 6 * hz
      | linear_combination -z ^ 7 * hz
      | linear_combination -z ^ 8 * hz
      | linear_combination -z ^ 9 * hz
      | linear_combination -z ^ 10 * hz
      | linear_combination -z ^ 11 * hz
      | linear_combination -z ^ 12 * hz
      | linear_combination -z ^ 13 * hz
      | linear_combination -z ^ 14 * hz
      | linear_combination -z ^ 15 * hz
      | linear_combination (-1 - z ^ 16) * hz

