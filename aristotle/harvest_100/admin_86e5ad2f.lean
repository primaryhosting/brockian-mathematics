import Mathlib
/-!
# Wiener Path Formula
Category: Chemistry
Target: Chem.wiener_path_formula
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset SimpleGraph

namespace Chem

/-- The Wiener index of a finite graph: the sum of the distances between all
unordered pairs of vertices.  It is computed here as half of the sum over all
ordered pairs. -/
noncomputable def wienerIndex {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ :=
  (∑ u : V, ∑ v : V, G.dist u v) / 2

/-- Any walk in the path graph is at least as long as the difference of the
indices of its endpoints. -/
lemma natDist_le_walk_length {n : ℕ} {i j : Fin n} (w : (pathGraph n).Walk i j) :
    Nat.dist (i : ℕ) (j : ℕ) ≤ w.length := by
  induction w with
  | nil => simp
  | cons h p ih =>
    rw [SimpleGraph.pathGraph_adj] at h
    simp only [SimpleGraph.Walk.length_cons]
    simp only [Nat.dist] at *
    omega

/-- In the path graph there is a walk of length `k` from `i` to `i + k`. -/
lemma exists_walk_pathGraph {n : ℕ} : ∀ (k : ℕ) (i j : Fin n), (j : ℕ) = (i : ℕ) + k →
    ∃ w : (pathGraph n).Walk i j, w.length = k := by
  intro k
  induction k with
  | zero =>
    intro i j h
    have : i = j := Fin.ext (by omega)
    subst this
    exact ⟨SimpleGraph.Walk.nil, rfl⟩
  | succ k ih =>
    intro i j h
    have hlt : (i : ℕ) + 1 < n := by omega
    let m : Fin n := ⟨(i : ℕ) + 1, hlt⟩
    have hadj : (pathGraph n).Adj i m := by
      rw [SimpleGraph.pathGraph_adj]; left; rfl
    obtain ⟨w, hw⟩ := ih m j (by simp only [m]; omega)
    exact ⟨SimpleGraph.Walk.cons hadj w, by simp [hw]⟩

/-- The distance in the path graph `P n` between `i` and `j` is `|i - j|`. -/
lemma pathGraph_dist {n : ℕ} (i j : Fin n) :
    (pathGraph n).dist i j = Nat.dist (i : ℕ) (j : ℕ) := by
  have key : ∀ a b : Fin n, (a : ℕ) ≤ (b : ℕ) →
      (pathGraph n).dist a b = Nat.dist (a : ℕ) (b : ℕ) := by
    intro a b hab
    obtain ⟨w, hw⟩ := exists_walk_pathGraph ((b : ℕ) - (a : ℕ)) a b (by omega)
    refine le_antisymm ?_ ?_
    · have := SimpleGraph.dist_le w
      rw [hw] at this
      simpa [Nat.dist, Nat.sub_eq_zero_of_le hab] using this
    · obtain ⟨p, hp⟩ := (SimpleGraph.Walk.reachable w).exists_walk_length_eq_dist
      have := natDist_le_walk_length p
      omega
  rcases le_total (i : ℕ) (j : ℕ) with h | h
  · exact key i j h
  · rw [SimpleGraph.dist_comm, key j i h, Nat.dist_comm]

/-- Gauss-type sum: `∑_{i<n} (n - i) = C(n+1, 2)`. -/
lemma sum_natDist_range (n : ℕ) :
    ∑ i ∈ range n, Nat.dist i n = (n + 1).choose 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have h : ∀ i ∈ range n, Nat.dist i (n + 1) = Nat.dist i n + 1 := by
      intro i hi
      simp only [Finset.mem_range] at hi
      simp only [Nat.dist]
      omega
    rw [Finset.sum_congr rfl h, Finset.sum_add_distrib, ih]
    simp [Nat.dist, Nat.choose_succ_succ (n + 1) 1]
    ring

/-- The doubled Wiener sum of the path on `n` vertices. -/
lemma sum_sum_natDist (n : ℕ) :
    ∑ i ∈ range n, ∑ j ∈ range n, Nat.dist i j = 2 * (n + 1).choose 3 := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have h1 : ∀ i ∈ range n, ∑ j ∈ range (n + 1), Nat.dist i j
        = (∑ j ∈ range n, Nat.dist i j) + Nat.dist i n := fun i _ => Finset.sum_range_succ _ _
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, ih, Finset.sum_range_succ]
    have h2 : ∑ j ∈ range n, Nat.dist n j = ∑ j ∈ range n, Nat.dist j n :=
      Finset.sum_congr rfl fun j _ => Nat.dist_comm _ _
    rw [h2, sum_natDist_range n]
    have h3 : (n + 2).choose 3 = (n + 1).choose 2 + (n + 1).choose 3 := Nat.choose_succ_succ (n + 1) 2
    simp [Nat.dist_self, h3]
    ring

/-- **Wiener path formula**: the Wiener index of the path graph `P n` equals
`C(n+1, 3)`. -/
theorem wiener_path_formula (n : ℕ) :
    wienerIndex (pathGraph n) = (n + 1).choose 3 := by
  unfold wienerIndex
  have inner : ∀ u : Fin n,
      ∑ v : Fin n, (pathGraph n).dist u v = ∑ j ∈ range n, Nat.dist (u : ℕ) j := by
    intro u
    rw [← Fin.sum_univ_eq_sum_range (fun j => Nat.dist (u : ℕ) j) n]
    exact Finset.sum_congr rfl fun v _ => pathGraph_dist u v
  have h : ∑ u : Fin n, ∑ v : Fin n, (pathGraph n).dist u v = 2 * (n + 1).choose 3 := by
    rw [← sum_sum_natDist n]
    simp_rw [inner]
    exact Fin.sum_univ_eq_sum_range (fun i => ∑ j ∈ range n, Nat.dist i j) n
  rw [h]
  omega

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

