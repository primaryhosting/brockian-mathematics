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

noncomputable def C4Adj : Matrix (Fin 4) (Fin 4) ℂ := (SimpleGraph.cycleGraph 4).adjMatrix ℂ

/-- The Hückel eigenvalue predicted for the `k`-th molecular orbital of `C₄`:
`2 cos (2πk/4)`. -/
