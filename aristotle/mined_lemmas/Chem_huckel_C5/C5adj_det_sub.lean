import Mathlib

/-!
# Huckel C 5
Category: Chemistry
Target: Chem.huckel_C5
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

namespace Chem

open Matrix Complex

/-- Adjacency matrix of the cycle graph `C₅` (the Hückel matrix of the cyclopentadienyl
π-system in units where the Coulomb integral `α = 0` and the resonance integral `β = 1`). -/

theorem C5adj_det_sub (μ : ℂ) :
    (C5adj - μ • (1 : Matrix (Fin 5) (Fin 5) ℂ)).det = -(μ ^ 5 - 5 * μ ^ 3 + 5 * μ - 2) := by
  have h : (C5adj - μ • (1 : Matrix (Fin 5) (Fin 5) ℂ)) =
      !![-μ, 1, 0, 0, 1;
         1, -μ, 1, 0, 0;
         0, 1, -μ, 1, 0;
         0, 0, 1, -μ, 1;
         1, 0, 0, 1, -μ] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [C5adj]
  rw [h]
  simp +decide [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

