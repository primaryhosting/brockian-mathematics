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

lemma C18adj_mulVec (z : ℂ) (hz : z ^ 18 = 1) :
    C18adj *ᵥ (fun j : Fin 18 => z ^ j.val) = (z + z ^ 17) • (fun j : Fin 18 => z ^ j.val) := by
  funext i
  simpa [Matrix.mulVec, dotProduct] using key z hz i

