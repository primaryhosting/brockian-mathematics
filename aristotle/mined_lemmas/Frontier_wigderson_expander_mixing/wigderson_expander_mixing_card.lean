import Mathlib

/-!
# Wigderson Expander Mixing
Category: Frontier Abel
Target: Frontier.wigderson_expander_mixing
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

set_option maxHeartbeats 1000000

namespace Frontier

section Aux

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- Cauchy–Schwarz for finite sums, in absolute-value / square-root form. -/

theorem wigderson_expander_mixing_card {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) (hd : G.IsRegularOfDegree d)
    (lam : ℝ) (hlam : 0 ≤ lam)
    (hspec : ∀ v : V → ℝ, ∑ i, v i = 0 →
      Real.sqrt (∑ i, ((G.adjMatrix ℝ).mulVec v i) ^ 2) ≤ lam * Real.sqrt (∑ i, (v i) ^ 2))
    (S T : Finset V) :
    |((((S ×ˢ T).filter fun p => G.Adj p.1 p.2).card : ℝ))
        - d * S.card * T.card / (Fintype.card V)|
      ≤ lam * Real.sqrt (S.card * T.card) := by
  have hcount : ∑ x ∈ S, ∑ y ∈ T, (G.adjMatrix ℝ) x y
      = (((S ×ˢ T).filter fun p => G.Adj p.1 p.2).card : ℝ) := by
    rw [← Finset.sum_product']
    simp [SimpleGraph.adjMatrix_apply, Finset.sum_boole]
  rw [← hcount]
  exact wigderson_expander_mixing G d hd lam hlam hspec S T

/-- The spectral hypothesis of `Frontier.wigderson_expander_mixing` is satisfiable in a
nontrivial case: for the complete graph on two vertices (which is `1`-regular) the adjacency
matrix is an isometry, so `lam = 1` works.  This shows the mixing lemma above is not vacuous. -/
