/-
# Ramsey 3 4
Category: Pure Mathematics
Target: Math.ramsey_3_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Ramsey 3 4

We define the two-colour Ramsey number `Math.ramseyNumber` and prove `R(3,4) = 9`.
-/

open Finset SimpleGraph

namespace Math

/-- `Arrows n r s` says that every simple graph on `n` vertices contains either a clique of
size `r` or an independent set of size `s`, i.e. `n → (r, s)` in Ramsey arrow notation. -/

theorem isNIndepSet_insert {V : Type*} [DecidableEq V] {G : SimpleGraph V} {n : ℕ} {v : V}
    {T : Finset V} (hv : v ∉ T) (hadj : ∀ t ∈ T, ¬ G.Adj v t) (hT : G.IsNIndepSet n T) :
    G.IsNIndepSet (n + 1) (insert v T) := by
  refine ⟨?_, by rw [card_insert_of_notMem hv, hT.card_eq]⟩
  rw [coe_insert]
  refine (Set.pairwise_insert_of_symmetric ?_).2 ⟨hT.isIndepSet, ?_⟩
  · intro x y hxy hyx
    exact hxy hyx.symm
  · intro b hb _
    exact hadj b hb

/-! ### Every triangle-free graph on six vertices has an independent set of size three -/

