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
-/

open scoped BigOperators
open Complex

namespace Chem

/-- A primitive 18-th root of unity. -/

theorem huckel_C18_eigenvector (k : Fin 18) :
    (fun j : Fin 18 => ch (j * k)) ≠ 0 ∧
      Matrix.mulVec ((SimpleGraph.cycleGraph 18).adjMatrix ℂ) (fun j : Fin 18 => ch (j * k))
        = ((2 * Real.cos (2 * Real.pi * k.val / 18) : ℝ) : ℂ) • fun j : Fin 18 => ch (j * k) := by
  constructor
  · intro h
    exact ch_ne_zero (0 * k) (congrFun h 0)
  · funext u
    have hL : Matrix.mulVec ((SimpleGraph.cycleGraph 18).adjMatrix ℂ)
        (fun j : Fin 18 => ch (j * k)) u
        = ((SimpleGraph.cycleGraph 18).adjMatrix ℂ * V) u k := rfl
    rw [hL, adj_mul_V, Matrix.mul_diagonal]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [show V u k = ch (u * k) from rfl, mu, mul_comm]

/-- **Hückel theory for the C₁₈ annulene ring.**  The spectrum of the adjacency matrix of the
cycle graph `C₁₈` is exactly `{2 cos (2πk/18) | k = 0, …, 17}`. -/
