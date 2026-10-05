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

/-- The Wiener index of a graph on a linearly ordered finite vertex set: the sum of the
graph distances over all unordered pairs of distinct vertices. -/
noncomputable def wienerIndex {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) : ℕ :=
  ∑ p ∈ Finset.univ.filter (fun p : V × V => p.1 < p.2), G.dist p.1 p.2

/-- In the path graph, a walk between two vertices is at least as long as the difference of
the indices of its endpoints. -/
lemma natAbs_sub_le_walk_length {n : ℕ} :
    ∀ {i j : Fin n} (p : (pathGraph n).Walk i j), ((i : ℤ) - (j : ℤ)).natAbs ≤ p.length := by
  intro i j p
  induction p with
  | nil => simp
  | cons h p ih =>
      rw [SimpleGraph.pathGraph_adj] at h
      simp only [SimpleGraph.Walk.length_cons]
      omega

/-- Upper bound for the distance in the path graph. -/
lemma pathGraph_dist_le {n : ℕ} :
    ∀ (d : ℕ) (i j : Fin n), (j : ℕ) = (i : ℕ) + d → (pathGraph n).dist i j ≤ d := by
  intro d
  induction d with
  | zero =>
      intro i j h
      have : i = j := Fin.ext (by omega)
      simp [this]
  | succ d ih =>
      intro i j h
      have hlt : (i : ℕ) + 1 < n := by
        have := j.isLt
        omega
      set i' : Fin n := ⟨(i : ℕ) + 1, hlt⟩ with hi'
      have hadj : (pathGraph n).Adj i i' := SimpleGraph.pathGraph_adj.mpr (Or.inl rfl)
      have h1 : (pathGraph n).dist i i' ≤ 1 := by
        simpa using SimpleGraph.dist_le hadj.toWalk
      have h2 : (pathGraph n).dist i' j ≤ d := ih i' j (by simp [hi']; omega)
      have htri : (pathGraph n).dist i j ≤ (pathGraph n).dist i i' + (pathGraph n).dist i' j :=
        (SimpleGraph.pathGraph_preconnected n i i').dist_triangle_left j
      omega

/-- The distance between two vertices of the path graph is the absolute difference of their
indices. -/
lemma pathGraph_dist {n : ℕ} (i j : Fin n) :
    (pathGraph n).dist i j = ((i : ℤ) - (j : ℤ)).natAbs := by
  refine le_antisymm ?_ ?_
  · rcases le_total (i : ℕ) (j : ℕ) with hij | hij
    · have := pathGraph_dist_le ((j : ℕ) - (i : ℕ)) i j (by omega)
      omega
    · have := pathGraph_dist_le ((i : ℕ) - (j : ℕ)) j i (by omega)
      rw [SimpleGraph.dist_comm] at this
      omega
  · obtain ⟨p, hp⟩ :=
      (SimpleGraph.pathGraph_preconnected n i j).exists_walk_length_eq_dist
    have := natAbs_sub_le_walk_length p
    omega

/-- Auxiliary triangular-number sum. -/
lemma sum_range_sub (n : ℕ) : ∑ a ∈ Finset.range n, (n - a) = (n + 1).choose 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have : ∑ a ∈ Finset.range n, (n + 1 - a) = (∑ a ∈ Finset.range n, (n - a)) + n := by
        rw [show ∑ a ∈ Finset.range n, (n + 1 - a)
              = ∑ a ∈ Finset.range n, ((n - a) + 1) from
            Finset.sum_congr rfl (fun a ha => by
              simp only [Finset.mem_range] at ha; omega)]
        rw [Finset.sum_add_distrib]
        simp
      rw [this, ih]
      rw [Nat.choose_succ_succ' (n + 1) 1]
      simp [Nat.choose_one_right]
      omega

/-- The double sum computing the Wiener index of the path graph. -/
lemma sum_double_range (n : ℕ) :
    ∑ a ∈ Finset.range n, ∑ b ∈ Finset.range n, (if a < b then b - a else 0)
      = (n + 1).choose 3 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have hlast : ∑ b ∈ Finset.range (n + 1), (if n < b then b - n else 0) = 0 := by
        refine Finset.sum_eq_zero (fun b hb => ?_)
        simp only [Finset.mem_range] at hb
        have : ¬ n < b := by omega
        simp [this]
      have hrow : ∀ a ∈ Finset.range n,
          ∑ b ∈ Finset.range (n + 1), (if a < b then b - a else 0)
            = (∑ b ∈ Finset.range n, (if a < b then b - a else 0)) + (n - a) := by
        intro a ha
        simp only [Finset.mem_range] at ha
        rw [Finset.sum_range_succ]
        simp [ha]
      rw [Finset.sum_congr rfl hrow, hlast, Finset.sum_add_distrib, ih, sum_range_sub,
        add_zero]
      rw [Nat.choose_succ_succ' (n + 2) 2]
      omega

/-- **Wiener path formula**: the Wiener index of the path graph `P n` on `n` vertices equals
`(n+1).choose 3`. -/
theorem wiener_path_formula (n : ℕ) :
    wienerIndex (pathGraph n) = (n + 1).choose 3 := by
  rw [wienerIndex]
  have h1 : ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2),
      (pathGraph n).dist p.1 p.2
      = ∑ a : Fin n, ∑ b : Fin n, (if (a : ℕ) < (b : ℕ) then (b : ℕ) - (a : ℕ) else 0) := by
    rw [Finset.sum_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    rw [pathGraph_dist]
    by_cases h : a < b
    · have : (a : ℕ) < (b : ℕ) := h
      simp only [h, this, if_true]
      omega
    · have : ¬ (a : ℕ) < (b : ℕ) := h
      simp [h, this]
  rw [h1]
  rw [Fin.sum_univ_eq_sum_range (fun a => ∑ b : Fin n,
    (if a < (b : ℕ) then (b : ℕ) - a else 0)) n]
  have h2 : ∀ a : ℕ, (∑ b : Fin n, (if a < (b : ℕ) then (b : ℕ) - a else 0))
      = ∑ b ∈ Finset.range n, (if a < b then b - a else 0) := by
    intro a
    exact Fin.sum_univ_eq_sum_range (fun b => if a < b then b - a else 0) n
  simp only [h2]
  exact sum_double_range n

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

