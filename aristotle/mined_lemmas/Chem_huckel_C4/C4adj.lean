import Mathlib

/-!
# Huckel C 4
Category: Chemistry
Target: Chem.huckel_C4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Real Matrix

namespace Chem

/-- The adjacency matrix of the cycle graph `C₄` (the Hückel matrix of cyclobutadiene,
with `α = 0`, `β = 1`): vertices are `Fin 4` arranged in a cycle, and `i ~ j` iff
`j = i + 1` or `i = j + 1` (addition modulo `4`). -/

def C4adj : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun i j => if j = i + 1 ∨ i = j + 1 then 1 else 0

