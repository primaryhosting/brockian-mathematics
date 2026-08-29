/-
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open Complex Polynomial

namespace Chem

/-- A primitive 11-th root of unity. -/

theorem huckel_C11_spectrum (μ : ℂ) :
    μ ∈ spectrum ℂ ((SimpleGraph.cycleGraph 11).adjMatrix ℂ)
      ↔ ∃ k : Fin 11, μ = ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 11) : ℝ) : ℂ) := by
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, huckel_C11, Polynomial.IsRoot,
    Polynomial.eval_prod, Finset.prod_eq_zero_iff]
  simp [sub_eq_zero]

end Chem

