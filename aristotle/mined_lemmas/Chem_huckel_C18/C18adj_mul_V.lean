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

lemma C18adj_mul_V : C18adj * V = V * Matrix.diagonal lam := by
  ext i k
  have h := key (zeta ^ (k : ℕ)) (zeta_pow_pow_eighteen k) i
  simp [Matrix.mul_apply, V, Matrix.vandermonde, Matrix.diagonal, lam, ← pow_mul,
    Finset.sum_ite_eq'] at h ⊢
  simpa [mul_comm] using h

