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

theorem huckel_C4 :
    spectrum ℂ ((SimpleGraph.cycleGraph 4).adjMatrix ℂ)
      = Set.range fun k : Fin 4 => ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 4) : ℝ) : ℂ) := by
  have : (fun k : Fin 4 => ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 4) : ℝ) : ℂ)) = cosEig := rfl
  rw [this, range_cosEig, ← C4Adj, spectrum_C4Adj]

/-! ### The characteristic polynomial, which also records the multiplicities -/

