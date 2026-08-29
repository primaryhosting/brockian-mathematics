/-
# Huckel C 5
Category: Chemistry
Target: Chem.huckel_C5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

namespace Chem

open Matrix

/-- The adjacency matrix of the cycle graph `C₅` (the Hückel matrix of cyclopentadienyl
in units where the Coulomb integral `α` is `0` and the resonance integral `β` is `1`). -/

lemma C5_mulVec_root (μ : ℝ) (h : μ ^ 2 + μ - 1 = 0) :
    C5 *ᵥ ![2, μ, -1 - μ, -1 - μ, μ] = μ • ![2, μ, -1 - μ, -1 - μ, μ] := by
  ext i
  fin_cases i <;> simp [C5, Matrix.mulVec, dotProduct, Fin.sum_univ_five] <;> nlinarith [h]

/-- Every eigenvalue of `C5` is a root of `x³ - x² - 3x + 2 = (x - 2)(x² + x - 1)`. -/
