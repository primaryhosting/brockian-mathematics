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
noncomputable def wienerIndex {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ :=
  (∑ u : V, ∑ v : V, G.dist u v) / 2

/-- Any walk in the path graph is at least as long as the difference of the indices
of its endpoints. -/
theorem pathGraph_le_length_of_walk {n : ℕ} {u v : Fin n} (p : (pathGraph n).Walk u v) :
    Nat.dist u.val v.val ≤ p.length := by
  induction p with
  | nil => simp
  | @cons a b c h p ih =>
      have hb : Nat.dist a.val b.val = 1 := by
        rw [pathGraph_adj] at h
        rcases h with h | h <;> unfold Nat.dist <;> omega
      calc Nat.dist a.val c.val ≤ Nat.dist a.val b.val + Nat.dist b.val c.val :=
            Nat.dist.triangle_inequality _ _ _
        _ ≤ 1 + p.length := by rw [hb]; exact Nat.add_le_add_left ih 1
        _ = (SimpleGraph.Walk.cons h p).length := by simp [Nat.add_comm]

/-- The distance in the path graph is bounded above by the difference of indices. -/
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
theorem pathGraph_dist_eq {n : ℕ} (u v : Fin n) :
    (pathGraph n).dist u v = Nat.dist u.val v.val := by
  refine le_antisymm (pathGraph_dist_le u v) ?_
  obtain ⟨p, hp⟩ := (SimpleGraph.pathGraph_preconnected n u v).exists_walk_length_eq_dist
  rw [← hp]
  exact pathGraph_le_length_of_walk p

/-- Sum of `n - i` over `i < n` is `C(n+1, 2)`. -/
theorem sum_range_sub_eq_choose (n : ℕ) :
    ∑ i ∈ Finset.range n, (n - i) = Nat.choose (n + 1) 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ']
      have : ∀ i ∈ Finset.range n, (n + 1 - (i + 1)) = n - i := by
        intro i _; omega
      rw [Finset.sum_congr rfl this, ih]
      simp [Nat.choose_succ_succ (n + 1) 1, Nat.choose_one_right]
      omega

/-- The double sum of `Nat.dist` over `range n` equals `2 * C(n+1, 3)`. -/
theorem sum_nat_dist_range (n : ℕ) :
    ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, Nat.dist i j = 2 * Nat.choose (n + 1) 3 := by
  induction n with
  | zero => decide
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have h1 : ∀ i ∈ Finset.range n,
          ∑ j ∈ Finset.range (n + 1), Nat.dist i j
            = (∑ j ∈ Finset.range n, Nat.dist i j) + (n - i) := by
        intro i hi
        rw [Finset.sum_range_succ, Nat.dist_eq_sub_of_le (by simp at hi; omega)]
      rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, ih, sum_range_sub_eq_choose]
      have h2 : ∑ j ∈ Finset.range (n + 1), Nat.dist n j
          = Nat.choose (n + 1) 2 := by
        rw [Finset.sum_range_succ, Nat.dist_self, Nat.add_zero, ← sum_range_sub_eq_choose n]
        refine Finset.sum_congr rfl ?_
        intro i hi
        rw [Nat.dist_eq_sub_of_le_right (by simp at hi; omega)]
      rw [h2]
      have h3 : Nat.choose (n + 1 + 1) 3 = Nat.choose (n + 1) 2 + Nat.choose (n + 1) 3 := by
        rw [Nat.choose_succ_succ (n + 1) 2]
      omega

/-- **Wiener index of the path graph.** The Wiener index of `P n` is `C(n+1, 3)`. -/
theorem wiener_path_formula (n : ℕ) :
    wienerIndex (SimpleGraph.pathGraph n) = Nat.choose (n + 1) 3 := by
  have hsum : ∑ u : Fin n, ∑ v : Fin n, (pathGraph n).dist u v = 2 * Nat.choose (n + 1) 3 := by
    have hinner : ∀ u : Fin n, ∑ v : Fin n, (pathGraph n).dist u v
        = ∑ j ∈ Finset.range n, Nat.dist u.val j := by
      intro u
      rw [← Fin.sum_univ_eq_sum_range (fun j => Nat.dist u.val j) n]
      exact Finset.sum_congr rfl fun v _ => pathGraph_dist_eq u v
    rw [Finset.sum_congr rfl fun u _ => hinner u,
      Fin.sum_univ_eq_sum_range (fun i => ∑ j ∈ Finset.range n, Nat.dist i j) n,
      sum_nat_dist_range n]
  unfold wienerIndex
  rw [hsum]
  omega

end Chem

