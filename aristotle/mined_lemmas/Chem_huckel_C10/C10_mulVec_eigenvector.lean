/-
# Huckel C 10
Category: Chemistry
Target: Chem.huckel_C10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 10
Category: Chemistry
Target: Chem.huckel_C10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Matrix
open Complex

namespace Chem

/-- The adjacency matrix (Hückel matrix, with `α = 0`, `β = 1`) of the cycle graph `C₁₀`. -/

lemma C10_mulVec_eigenvector (k : Fin 10) :
    C10 *ᵥ (fun i : Fin 10 => zk k ^ (i : ℕ)) = mu k • fun i : Fin 10 => zk k ^ (i : ℕ) := by
  funext i
  rw [C10_mulVec]
  simpa [mul_comm, ← zk_add_inv k, zk_inv_eq k] using pow_shift_eq (zk k) (zk_pow_ten k) i

/-- **The Hückel spectrum of `C₁₀`.**  The eigenvalues of the adjacency matrix of the cycle
graph on 10 vertices are exactly the numbers `2 cos (2πk/10)`, `k = 0, …, 9`. -/
