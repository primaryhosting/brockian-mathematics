import Mathlib

/-!
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Matrix Finset Polynomial

set_option maxHeartbeats 1000000

/-! ## Generalities on eigenvalues of matrices -/

/-- A scalar `μ` is an eigenvalue of `M` iff `M - μ • 1` is singular. -/

lemma AC_eq_map : AC = Complex.ofRealHom.mapMatrix ((SimpleGraph.cycleGraph 20).adjMatrix ℝ) := by
  ext i j
  simp [AC, SimpleGraph.adjMatrix_apply]

/-- **Hückel theory for C₂₀.** The eigenvalues of the adjacency matrix of the cycle graph
`C₂₀` (the Hückel matrix of the annulene C₂₀, in units of `β`, with `α = 0`) are exactly the
numbers `2 cos (2πk/20)` for `k = 0, …, 19`. -/
