/-
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
open scoped BigOperators
open scoped Real

namespace Chem

open Complex Matrix SimpleGraph

/-- A primitive 20-th root of unity. -/

lemma adj_mul_U : ((SimpleGraph.cycleGraph 20).adjMatrix ℂ) * U = U * D := by
  ext i k
  have hcol : (fun j => U j k) = evec k := funext fun j => U_apply j k
  have h1 : (((SimpleGraph.cycleGraph 20).adjMatrix ℂ) * U) i k
      = ((SimpleGraph.cycleGraph 20).adjMatrix ℂ).mulVec (evec k) i := by
    rw [Matrix.mul_apply, ← hcol]
    rfl
  rw [h1, evec_eigen, Pi.smul_apply, smul_eq_mul, D, Matrix.mul_diagonal, U_apply,
    mul_comm]

/-- **Hückel theory for C₂₀.**  A complex number `μ` is an eigenvalue of the adjacency matrix
of the cycle graph `C₂₀` if and only if it is of the form `2 cos (2πk/20)` for some
`k ∈ {0, …, 19}`. -/
