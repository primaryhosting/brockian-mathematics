/-
# Huckel C 4
Category: Chemistry
Target: Chem.huckel_C4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Matrix

namespace Chem

/-- The adjacency matrix (Hückel matrix with `α = 0`, `β = 1`) of the cycle graph `C₄`. -/

lemma mem_spectrum_iff_det_eq_zero (r : ℂ) :
    r ∈ spectrum ℂ C4Adj ↔ (r • (1 : Matrix (Fin 4) (Fin 4) ℂ) - C4Adj).det = 0 := by
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_ne_iff,
    Algebra.algebraMap_eq_smul_one]

