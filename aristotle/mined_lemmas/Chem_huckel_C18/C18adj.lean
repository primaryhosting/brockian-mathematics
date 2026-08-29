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

The Hückel model for the annulene `C₁₈` uses the adjacency matrix of the cycle
graph `C₁₈`.  We show that its eigenvalues are exactly the `18` numbers
`2 cos (2πk/18)`, `k = 0, …, 17`.
-/

namespace Chem

open Complex Matrix

/-- The adjacency matrix of the cycle graph `C₁₈` on the vertex set `Fin 18`:
vertices `i` and `j` are adjacent iff they are consecutive modulo `18`. -/

noncomputable def C18adj : Matrix (Fin 18) (Fin 18) ℂ :=
  Matrix.of fun i j => if j.val = (i.val + 1) % 18 ∨ i.val = (j.val + 1) % 18 then 1 else 0

/-- The primitive 18-th root of unity `exp (2πi/18)`. -/
