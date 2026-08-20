/-
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Chem

open Polynomial Matrix

/-! ### The 20-th root of unity and the characters of `Fin 20` -/

/-- The primitive 20-th root of unity `exp (2πi/20)`. -/

theorem huckel_C20 :
    ((SimpleGraph.cycleGraph 20).adjMatrix ℂ).charpoly
      = ∏ k : Fin 20,
          (Polynomial.X - Polynomial.C ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 20) : ℝ) : ℂ)) := by
  obtain ⟨U, hU⟩ := isUnit_Fmat
  have hA : (SimpleGraph.cycleGraph 20).adjMatrix ℂ = (U : Matrix (Fin 20) (Fin 20) ℂ) * Dmat *
      ((U⁻¹ : (Matrix (Fin 20) (Fin 20) ℂ)ˣ) : Matrix (Fin 20) (Fin 20) ℂ) := by
    have h1 : (SimpleGraph.cycleGraph 20).adjMatrix ℂ * (U : Matrix (Fin 20) (Fin 20) ℂ)
        = (U : Matrix (Fin 20) (Fin 20) ℂ) * Dmat := by
      rw [hU]; exact adj_mul_Fmat
    calc (SimpleGraph.cycleGraph 20).adjMatrix ℂ
        = (SimpleGraph.cycleGraph 20).adjMatrix ℂ * (U : Matrix (Fin 20) (Fin 20) ℂ) *
            ((U⁻¹ : (Matrix (Fin 20) (Fin 20) ℂ)ˣ) : Matrix (Fin 20) (Fin 20) ℂ) := by
          rw [mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
      _ = _ := by rw [h1]
  rw [hA, Matrix.charpoly_units_conj U Dmat, Dmat, Matrix.charpoly_diagonal]

/-- The spectrum of the adjacency matrix of `C₂₀` is exactly the set of Hückel eigenvalues
`2·cos(2πk/20)`, `k = 0, …, 19`. -/
