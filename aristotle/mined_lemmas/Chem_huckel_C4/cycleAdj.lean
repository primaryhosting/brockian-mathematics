/-
# Huckel C 4
Category: Chemistry
Target: Chem.huckel_C4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Huckel C 4
Category: Chemistry
Target: Chem.huckel_C4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Polynomial Real

/-- Adjacency matrix of the cycle graph `C n` on the vertex set `Fin n`:
vertices `i` and `j` are adjacent iff they are consecutive modulo `n`. -/

def cycleAdj (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if (i.val + 1) % n = j.val ∨ (j.val + 1) % n = i.val then 1 else 0

/-- Explicit form of the adjacency matrix of `C 4`. -/
