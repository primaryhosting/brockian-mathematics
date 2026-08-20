import Mathlib

/-!
# Huckel C 9
Category: Chemistry
Target: Chem.huckel_C9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Real
open Complex Polynomial

namespace Chem

/-- A primitive 9th root of unity. -/

theorem adj_mul_Vm :
    (SimpleGraph.cycleGraph 9).adjMatrix ℂ * Vm = Vm * Matrix.diagonal lam := by
  ext j k
  rw [Matrix.mul_apply, adj_sum j (fun l => Vm l k), Matrix.mul_diagonal]
  have h1 : ((j + 1 : Fin 9) : ℕ) = ((j : ℕ) + 1) % 9 := by revert j; decide
  have h2 : ((j - 1 : Fin 9) : ℕ) = ((j : ℕ) + 8) % 9 := by revert j; decide
  have e1 : Vm (j + 1) k = om ^ ((j : ℕ) * (k : ℕ)) * om ^ ((k : ℕ)) := by
    simp only [Vm, h1, ← pow_add]
    refine om_pow_congr ?_
    have h := Nat.ModEq.mul_right ((k : ℕ)) (Nat.mod_modEq ((j : ℕ) + 1) 9)
    rw [show ((j : ℕ) + 1) * (k : ℕ) = (j : ℕ) * (k : ℕ) + (k : ℕ) from by ring] at h
    exact h
  have e2 : Vm (j - 1) k = om ^ ((j : ℕ) * (k : ℕ)) * om ^ (8 * (k : ℕ)) := by
    simp only [Vm, h2, ← pow_add]
    refine om_pow_congr ?_
    have h := Nat.ModEq.mul_right ((k : ℕ)) (Nat.mod_modEq ((j : ℕ) + 8) 9)
    rw [show ((j : ℕ) + 8) * (k : ℕ) = (j : ℕ) * (k : ℕ) + 8 * (k : ℕ) from by ring] at h
    exact h
  rw [e1, e2, ← mul_add, om_pow_add_inv k]
  rfl

/-- **Hückel theory for C₉.**  The characteristic polynomial of the adjacency matrix of the
cycle graph `C₉` factors as `∏_{k=0}^{8} (X - 2 cos (2πk/9))`, i.e. its eigenvalues are exactly
`2 cos (2πk/9)` for `k = 0, …, 8`. -/
