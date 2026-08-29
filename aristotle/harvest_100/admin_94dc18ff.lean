/-
# Wiener Path Formula
Category: Chemistry
Target: Chem.wiener_path_formula
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Finset SimpleGraph

namespace Chem

/-- The Wiener index of a finite graph: the sum of the distances over all unordered
pairs of distinct vertices (represented as ordered pairs `u < v`). -/
noncomputable def wienerIndex {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) : ℕ :=
  ∑ p ∈ Finset.univ.filter (fun p : V × V => p.1 < p.2), G.dist p.1 p.2

/-! ### Distances in the path graph -/

/-- In the path graph, there is a walk of length `k` from `u` to `v` whenever `v = u + k`. -/
theorem exists_walk_pathGraph (n : ℕ) :
    ∀ (k : ℕ) (u v : Fin n), (v : ℕ) = (u : ℕ) + k →
      ∃ w : (pathGraph n).Walk u v, w.length = k := by
  intro k
  induction k with
  | zero =>
      intro u v h
      have : u = v := Fin.ext (by omega)
      subst this
      exact ⟨SimpleGraph.Walk.nil, rfl⟩
  | succ k ih =>
      intro u v h
      have hv : (v : ℕ) < n := v.isLt
      have hm : (u : ℕ) + k < n := by omega
      obtain ⟨w, hw⟩ := ih u ⟨(u : ℕ) + k, hm⟩ rfl
      have hadj : (pathGraph n).Adj (⟨(u : ℕ) + k, hm⟩ : Fin n) v := by
        rw [SimpleGraph.pathGraph_adj]
        exact Or.inl (show (u : ℕ) + k + 1 = (v : ℕ) by omega)
      exact ⟨w.append (SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil), by
        simp [SimpleGraph.Walk.length_append, hw]⟩

/-- Any two vertices of a path graph are joined by a walk. -/
theorem pathGraph_reachable (n : ℕ) (u v : Fin n) : (pathGraph n).Reachable u v := by
  rcases le_total (u : ℕ) (v : ℕ) with h | h
  · obtain ⟨w, _⟩ := exists_walk_pathGraph n ((v : ℕ) - (u : ℕ)) u v (by omega)
    exact ⟨w⟩
  · obtain ⟨w, _⟩ := exists_walk_pathGraph n ((u : ℕ) - (v : ℕ)) v u (by omega)
    exact ⟨w.reverse⟩

/-- Any walk in the path graph has length at least the numeric distance of its endpoints. -/
theorem natDist_le_walk_length {n : ℕ} {u v : Fin n} (w : (pathGraph n).Walk u v) :
    Nat.dist (u : ℕ) (v : ℕ) ≤ w.length := by
  induction w with
  | nil => simp [Nat.dist_self]
  | cons h p ih =>
      rw [SimpleGraph.pathGraph_adj] at h
      simp only [SimpleGraph.Walk.length_cons]
      simp only [Nat.dist] at ih ⊢
      omega

/-- The distance between two vertices of the path graph is the numeric distance of their
indices. -/
theorem pathGraph_dist (n : ℕ) (u v : Fin n) :
    (pathGraph n).dist u v = Nat.dist (u : ℕ) (v : ℕ) := by
  refine le_antisymm ?_ ?_
  · rcases le_total (u : ℕ) (v : ℕ) with h | h
    · obtain ⟨w, hw⟩ := exists_walk_pathGraph n ((v : ℕ) - (u : ℕ)) u v (by omega)
      have hle := SimpleGraph.dist_le w
      rw [hw] at hle
      simp only [Nat.dist]
      omega
    · obtain ⟨w, hw⟩ := exists_walk_pathGraph n ((u : ℕ) - (v : ℕ)) v u (by omega)
      have hle := SimpleGraph.dist_le w
      rw [hw, SimpleGraph.dist_comm] at hle
      simp only [Nat.dist]
      omega
  · obtain ⟨w, hw⟩ := (pathGraph_reachable n u v).exists_walk_length_eq_dist
    calc Nat.dist (u : ℕ) (v : ℕ) ≤ w.length := natDist_le_walk_length w
      _ = (pathGraph n).dist u v := hw

/-! ### The combinatorial identities -/

theorem sum_range_sub (n : ℕ) : ∑ i ∈ range n, (n - i) = (n + 1).choose 2 := by
  induction n with
  | zero => decide
  | succ n ih =>
      rw [Finset.sum_range_succ']
      have h1 : ∑ i ∈ range n, (n + 1 - (i + 1)) = ∑ i ∈ range n, (n - i) :=
        Finset.sum_congr rfl (fun i _ => by omega)
      have h2 : (n + 1 + 1).choose 2 = (n + 1).choose 1 + (n + 1).choose 2 :=
        Nat.choose_succ_succ (n + 1) 1
      rw [Nat.choose_one_right] at h2
      rw [h1, ih]
      omega

theorem sum_double_range (n : ℕ) :
    ∑ j ∈ range n, ∑ i ∈ range j, (j - i) = (n + 1).choose 3 := by
  induction n with
  | zero => decide
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, sum_range_sub]
      have h3 : (n + 1 + 1).choose 3 = (n + 1).choose 2 + (n + 1).choose 3 :=
        Nat.choose_succ_succ (n + 1) 2
      omega

/-! ### The Wiener index of the path graph -/

/-- **Wiener path formula**: the Wiener index of the path graph `P n` is `C(n+1, 3)`. -/
theorem wiener_path_formula (n : ℕ) :
    wienerIndex (SimpleGraph.pathGraph n) = (n + 1).choose 3 := by
  rw [wienerIndex]
  have h1 : ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2),
      (pathGraph n).dist p.1 p.2
      = ∑ i : Fin n, ∑ j : Fin n, (if (i : ℕ) < (j : ℕ) then (j : ℕ) - (i : ℕ) else 0) := by
    rw [Finset.sum_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    simp only [Fin.lt_def]
    by_cases h : (i : ℕ) < (j : ℕ)
    · rw [if_pos h, if_pos h, pathGraph_dist]
      simp only [Nat.dist]
      omega
    · rw [if_neg h, if_neg h]
  rw [h1]
  have h2 : ∑ i : Fin n, ∑ j : Fin n, (if (i : ℕ) < (j : ℕ) then (j : ℕ) - (i : ℕ) else 0)
      = ∑ i ∈ range n, ∑ j ∈ range n, (if i < j then j - i else 0) := by
    rw [Fin.sum_univ_eq_sum_range
      (fun i => ∑ j : Fin n, (if i < (j : ℕ) then (j : ℕ) - i else 0)) n]
    exact Finset.sum_congr rfl
      (fun i _ => Fin.sum_univ_eq_sum_range (fun j => if i < j then j - i else 0) n)
  rw [h2, Finset.sum_comm, ← sum_double_range n]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨fun h => h.2, fun h => ⟨lt_trans h (Finset.mem_range.mp hj), h⟩⟩

end Chem

import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

