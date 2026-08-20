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

/-- The Wiener index of a finite graph: the sum of the graph distances over all
unordered pairs of distinct vertices (indexed here by ordered pairs `i < j`). -/
noncomputable def wiener {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) : ℕ :=
  ∑ i : V, ∑ j ∈ Finset.univ.filter (fun j => i < j), G.dist i j

/-- Any walk in the path graph is at least as long as the numeric distance of its endpoints. -/
lemma nat_dist_le_walk_length {n : ℕ} {i j : Fin n} (w : (pathGraph n).Walk i j) :
    Nat.dist (i : ℕ) (j : ℕ) ≤ w.length := by
  induction w with
  | nil => simp [Nat.dist]
  | @cons a b c h p ih =>
      rw [SimpleGraph.Walk.length_cons]
      rw [SimpleGraph.pathGraph_adj] at h
      simp only [Nat.dist] at *
      omega

/-- Upper bound on the distance in the path graph. -/
lemma pathGraph_dist_le (n : ℕ) :
    ∀ (k : ℕ) (i j : Fin n), (j : ℕ) = (i : ℕ) + k → (pathGraph n).dist i j ≤ k := by
  intro k
  induction k with
  | zero =>
      intro i j h
      have : i = j := Fin.ext (by omega)
      simp [this]
  | succ k ih =>
      intro i j h
      have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le _) i.isLt
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      have hij : (i : ℕ) + 1 < m + 1 := by
        have := j.isLt; omega
      set i' : Fin (m + 1) := ⟨(i : ℕ) + 1, hij⟩ with hi'
      have hadj : (pathGraph (m + 1)).Adj i i' := by
        rw [SimpleGraph.pathGraph_adj]
        left
        simp [hi']
      have h1 : (pathGraph (m + 1)).dist i i' = 1 :=
        (SimpleGraph.dist_eq_one_iff_adj).2 hadj
      have h2 : (pathGraph (m + 1)).dist i' j ≤ k := ih i' j (by simp [hi']; omega)
      have := (pathGraph_connected m).dist_triangle (u := i) (v := i') (w := j)
      omega

/-- The distance between two vertices of the path graph is the numeric distance of their labels. -/
lemma pathGraph_dist (n : ℕ) (i j : Fin n) :
    (pathGraph n).dist i j = Nat.dist (i : ℕ) (j : ℕ) := by
  have hle : (pathGraph n).dist i j ≤ Nat.dist (i : ℕ) (j : ℕ) := by
    rcases le_total (i : ℕ) (j : ℕ) with hij | hij
    · have := pathGraph_dist_le n (Nat.dist (i : ℕ) (j : ℕ)) i j (by simp [Nat.dist]; omega)
      exact this
    · have := pathGraph_dist_le n (Nat.dist (i : ℕ) (j : ℕ)) j i (by simp [Nat.dist]; omega)
      rw [SimpleGraph.dist_comm]
      simpa [Nat.dist_comm] using this
  have hge : Nat.dist (i : ℕ) (j : ℕ) ≤ (pathGraph n).dist i j := by
    have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le _) i.isLt
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    obtain ⟨w, hw⟩ := (pathGraph_connected m).exists_walk_length_eq_dist i j
    rw [← hw]
    exact nat_dist_le_walk_length w
  omega

/-- Gauss' sum as a binomial coefficient. -/
lemma sum_range_id_eq_choose (m : ℕ) : ∑ i ∈ Finset.range m, i = m.choose 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih, Nat.choose_succ_succ m 1]
      simp [Nat.add_comm]

/-- The auxiliary summand: `g i j = j - i` for `i < j`, and `0` otherwise. -/
private def g (i j : ℕ) : ℕ := if i < j then j - i else 0

lemma sum_g_col (n : ℕ) : ∑ i ∈ Finset.range n, g i n = (n + 1).choose 2 := by
  have h1 : ∑ i ∈ Finset.range n, g i n = ∑ i ∈ Finset.range n, (i + 1) := by
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [Finset.mem_range] at hi
    simp only [g]
    rw [if_pos (by omega)]
    omega
  rw [h1, Finset.sum_add_distrib, sum_range_id_eq_choose, Finset.sum_const, Finset.card_range,
    smul_eq_mul, mul_one, Nat.choose_succ_succ n 1]
  simp [Nat.add_comm]

lemma sum_g_double (n : ℕ) :
    ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, g i j = (n + 1).choose 3 := by
  induction n with
  | zero => decide
  | succ n ih =>
      have hrow : ∑ j ∈ Finset.range n, g n j = 0 := by
        refine Finset.sum_eq_zero fun j hj => ?_
        simp only [Finset.mem_range] at hj
        simp only [g]
        rw [if_neg (by omega)]
      have hgnn : g n n = 0 := by simp [g]
      calc ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1), g i j
          = ∑ i ∈ Finset.range (n + 1), ((∑ j ∈ Finset.range n, g i j) + g i n) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.sum_range_succ]
        _ = (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range n, g i j)
              + ∑ i ∈ Finset.range (n + 1), g i n := Finset.sum_add_distrib
        _ = ((∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, g i j) + ∑ j ∈ Finset.range n, g n j)
              + ((∑ i ∈ Finset.range n, g i n) + g n n) := by
            rw [Finset.sum_range_succ, Finset.sum_range_succ]
        _ = (n + 1).choose 3 + (n + 1).choose 2 := by
            rw [ih, hrow, hgnn, sum_g_col]; omega
        _ = (n + 1 + 1).choose 3 := by
            have h := Nat.choose_succ_succ (n + 1) 2
            norm_num at h
            omega

/-- **The Wiener index of the path graph `P n` is `C(n+1, 3)`.** -/
theorem wiener_path_formula (n : ℕ) : wiener (pathGraph n) = (n + 1).choose 3 := by
  have key : wiener (pathGraph n) = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, g i j := by
    rw [wiener]
    rw [← Fin.sum_univ_eq_sum_range (fun i => ∑ j ∈ Finset.range n, g i j) n]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_filter, ← Fin.sum_univ_eq_sum_range (fun j => g (i : ℕ) j) n]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pathGraph_dist]
    by_cases hij : i < j
    · have : (i : ℕ) < (j : ℕ) := hij
      simp only [if_pos hij, g, if_pos this, Nat.dist]
      omega
    · have : ¬ ((i : ℕ) < (j : ℕ)) := hij
      simp only [if_neg hij, g, if_neg this]
  rw [key, sum_g_double]

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

