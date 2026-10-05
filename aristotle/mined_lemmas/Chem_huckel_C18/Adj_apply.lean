/-
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses `/-` rather than `/-!` only because Lean 4 does not allow a module
-- docstring to precede the `import` commands; the same header is repeated below verbatim.)

import Mathlib

/-!
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
The Hückel (tight-binding) Hamiltonian of the cyclic polyene `C₁₈` is, up to the affine
normalisation `H = α + β A`, the adjacency matrix `A` of the cycle graph `C₁₈`.
We prove that a complex number `μ` is an eigenvalue of that adjacency matrix precisely when
`μ = 2 cos (2πk/18)` for some `k ∈ {0, …, 17}`.

The vertex type of `SimpleGraph.cycleGraph 18` is `Fin 18`, which is `ZMod 18`; all index
arithmetic below is therefore modulo `18`.
-/

namespace Chem

open Complex Matrix Finset

/-- A primitive 18-th root of unity. -/

lemma Adj_apply (i j : ZMod 18) : Adj i j = if i - j = 1 ∨ j - i = 1 then 1 else 0 := by
  simp [Adj, SimpleGraph.adjMatrix_apply, SimpleGraph.cycleGraph_adj]

