/-
# Huang Sensitivity
Category: Frontier — Fields Medal Work
Target: Frontier.huang_sensitivity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean 4 requires `import` commands to precede every other command, including module
-- docstrings, so the header above is repeated as a module docstring after the imports.)

import Mathlib
import Archive.Sensitivity

/-!
# Huang Sensitivity
Category: Frontier — Fields Medal Work
Target: Frontier.huang_sensitivity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-- Two vertices of the Boolean hypercube `{0,1}^n = (Fin n → Bool)` are adjacent when they
differ in exactly one coordinate. -/

lemma nbhd_eq_inter_adjacent {n : ℕ} (H : Set (Sensitivity.Q n)) (q : Sensitivity.Q n) :
    nbhd H q = H ∩ q.adjacent := by
  ext p
  simp only [nbhd, Set.mem_setOf_eq, Set.mem_inter_iff, Sensitivity.Q.adjacent,
    Set.mem_setOf_eq, and_congr_right_iff]
  intro _
  exact hammingAdjacent_comm p q

/-- **Huang's sensitivity theorem** (Hao Huang, 2019), in its combinatorial "degree" form:
in the `n`-dimensional Boolean hypercube with `n ≥ 1`, any set `H` of more than half of the
`2 ^ n` vertices contains a vertex having at least `√n` neighbours inside `H`.

Equivalently: every induced subgraph of the `n`-cube on more than `2 ^ (n - 1)` vertices has
maximum degree at least `√n`.  This is the statement from which the polynomial relation between
the sensitivity and the degree of a Boolean function follows (`s(f) ≥ √(deg f)`, hence
`deg f ≤ s(f) ^ 2`).

The proof is obtained from the formalization of Huang's theorem in the Mathlib archive,
`Sensitivity.huang_degree_theorem` (Barton, Commelin, Han, Hughes, Lewis, Massot). -/
