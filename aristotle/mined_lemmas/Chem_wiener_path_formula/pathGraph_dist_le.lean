/-
# Wiener Path Formula
Category: Chemistry
Target: Chem.wiener_path_formula
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Wiener Path Formula
Category: Chemistry
Target: Chem.wiener_path_formula
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

namespace Chem

open SimpleGraph Finset

/-- The Wiener index of a finite graph: the sum of the distances between all
unordered pairs of vertices, i.e. half the sum of `dist u v` over all ordered pairs. -/

theorem pathGraph_dist_le {n : ℕ} (u v : Fin n) :
    (pathGraph n).dist u v ≤ Nat.dist u.val v.val := by
  -- induct on the gap
  suffices h : ∀ k : ℕ, ∀ u v : Fin n, v.val = u.val + k → (pathGraph n).dist u v ≤ k by
    rcases le_total u.val v.val with hle | hle
    · have := h (v.val - u.val) u v (by omega)
      rwa [Nat.dist_eq_sub_of_le hle]
    · have := h (u.val - v.val) v u (by omega)
      rw [Nat.dist_eq_sub_of_le_right hle, SimpleGraph.dist_comm]
      exact this
  intro k
  induction k with
  | zero =>
      intro u v hv
      have : u = v := Fin.ext (by omega)
      simp [this]
  | succ k ih =>
      intro u v hv
      have hlt : u.val + 1 < n := by omega
      set w : Fin n := ⟨u.val + 1, hlt⟩ with hw
      have hadj : (pathGraph n).Adj u w := by
        rw [pathGraph_adj]; left; simp [hw]
      have h1 : (pathGraph n).dist u w = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hadj
      have h2 : (pathGraph n).dist w v ≤ k := ih w v (by simp [hw]; omega)
      have htri : (pathGraph n).dist u v ≤ (pathGraph n).dist u w + (pathGraph n).dist w v :=
        (SimpleGraph.pathGraph_preconnected n u w).dist_triangle_left v
      omega

/-- Key intermediate lemma: the distance between two vertices of the path graph `P n`
is the absolute difference of their indices. -/
