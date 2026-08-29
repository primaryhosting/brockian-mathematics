/-
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Hückel theory for the cycle C₁₁

The adjacency eigenvalues of the cycle graph `C₁₁` are exactly `2 cos (2πk/11)`, `k = 0,…,10`.
-/

open Complex Matrix Finset

namespace Chem

instance : Fact (Nat.Prime 11) := ⟨by norm_num⟩

/-! ## The cycle graph and its adjacency matrix -/

/-- The cycle graph on 11 vertices, realised on `ZMod 11`: `i ~ j` iff `i - j = ±1`. -/

theorem C11_eq_cycleGraph : C11 = (SimpleGraph.cycleGraph 11 : SimpleGraph (Fin 11)) := by
  ext i j
  rw [SimpleGraph.cycleGraph_adj']
  show (i - j = 1 ∨ j - i = 1) ↔ _
  revert i j
  decide

/-- The adjacency (Hückel) matrix of `C₁₁`. -/
