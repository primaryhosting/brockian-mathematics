import Mathlib

/-!
# Wiener Path Formula
Category: Chemistry
Target: Chem.wiener_path_formula
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Finset SimpleGraph

namespace Chem

/-- The Wiener index of a finite graph: the sum of the graph distances over all unordered
pairs of vertices.  It is computed here as half of the sum of `G.dist u v` over all ordered
pairs `(u, v)`. -/

theorem pathGraph_dist_le_of_add {n : ℕ} :
    ∀ (d : ℕ) (u v : Fin n), v.val = u.val + d → (pathGraph n).dist u v ≤ d := by
  intro d
  induction d with
  | zero =>
      intro u v h
      have huv : u = v := Fin.ext (by omega)
      simp [huv]
  | succ d ih =>
      intro u v h
      have hlt : u.val + d < n := by omega
      set w : Fin n := ⟨u.val + d, hlt⟩ with hw
      have hwval : w.val = u.val + d := rfl
      have h1 : (pathGraph n).dist u w ≤ d := ih u w hwval
      have hadj : (pathGraph n).Adj w v := by
        rw [SimpleGraph.pathGraph_adj]
        exact Or.inl (by omega)
      have h2 : (pathGraph n).dist w v = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hadj
      have hr : (pathGraph n).Reachable u w := SimpleGraph.pathGraph_preconnected n u w
      have h3 := hr.dist_triangle_left v
      omega

/-- The distance between two vertices of the path graph `P n` is the absolute difference of
their indices. -/
