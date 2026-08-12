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

namespace Chem

open Finset SimpleGraph

/-- The Wiener index of a finite graph: the sum of the distances over all
unordered pairs of distinct vertices (represented as ordered pairs `u < v`). -/
noncomputable def wienerIndex {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) : ℕ :=
  ∑ p ∈ (Finset.univ : Finset (V × V)) with p.1 < p.2, G.dist p.1 p.2

/-- Any walk in the path graph between `u` and `v` has length at least `|u - v|`. -/
lemma pathGraph_le_walk_length {n : ℕ} {u v : Fin n} (p : (pathGraph n).Walk u v) :
    |((u : ℕ) : ℤ) - ((v : ℕ) : ℤ)| ≤ (p.length : ℤ) := by
  induction p with
  | nil => simp
  | @cons a b c h p ih =>
    rw [pathGraph_adj] at h
    simp only [SimpleGraph.Walk.length_cons, Nat.cast_add, Nat.cast_one]
    rcases abs_cases (((a : ℕ) : ℤ) - ((c : ℕ) : ℤ)) with ⟨e1, _⟩ | ⟨e1, _⟩ <;>
      rcases abs_cases (((b : ℕ) : ℤ) - ((c : ℕ) : ℤ)) with ⟨e2, _⟩ | ⟨e2, _⟩ <;>
      omega

lemma pathGraph_dist_le {n : ℕ} : ∀ (k : ℕ) (u v : Fin n), (v : ℕ) = (u : ℕ) + k →
    (pathGraph n).dist u v ≤ k := by
  intro k
  induction k with
  | zero =>
    intro u v h
    have : u = v := Fin.ext (by omega)
    simp [this]
  | succ k ih =>
    intro u v h
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := v.isLt; omega⟩
    have hw : (u : ℕ) + k < m + 1 := by have := v.isLt; omega
    set w : Fin (m + 1) := ⟨(u : ℕ) + k, hw⟩ with hwdef
    have hadj : (pathGraph (m + 1)).Adj w v := by
      rw [pathGraph_adj]
      left
      simp only [hwdef]
      omega
    have h1 : (pathGraph (m + 1)).dist w v = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr hadj
    have h2 : (pathGraph (m + 1)).dist u w ≤ k := ih u w (by simp [hwdef])
    have := (pathGraph_connected m).dist_triangle (u := u) (v := w) (w := v)
    omega

/-- The distance in the path graph is the difference of the indices. -/
theorem pathGraph_dist_of_le {n : ℕ} (u v : Fin n) (h : (u : ℕ) ≤ (v : ℕ)) :
    (pathGraph n).dist u v = (v : ℕ) - (u : ℕ) := by
  refine le_antisymm (pathGraph_dist_le _ u v (by omega)) ?_
  by_cases hr : (pathGraph n).Reachable u v
  · obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_dist
    have := pathGraph_le_walk_length p
    rw [hp] at this
    rcases abs_cases (((u : ℕ) : ℤ) - ((v : ℕ) : ℤ)) with ⟨e1, _⟩ | ⟨e1, _⟩ <;> omega
  · exact absurd ((pathGraph_preconnected n) u v) hr

lemma sum_range_sub (n : ℕ) : ∑ a ∈ Finset.range n, (n - a) = (n + 1).choose 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have key : ∀ a ∈ Finset.range n, n + 1 - a = (n - a) + 1 := by
      intro a ha
      simp only [Finset.mem_range] at ha
      omega
    rw [Finset.sum_congr rfl key, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one, ih,
      Nat.choose_succ_succ (n + 1) 1, Nat.choose_one_right]
    norm_num
    omega

lemma double_sum_eq (n : ℕ) :
    ∑ a ∈ Finset.range n, ∑ b ∈ Finset.range n, (if a < b then b - a else 0)
      = (n + 1).choose 3 := by
  induction n with
  | zero => simp [Nat.choose]
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have h2 : ∑ b ∈ Finset.range (n + 1), (if n < b then b - n else 0) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro b hb
      simp only [Finset.mem_range] at hb
      rw [if_neg (by omega)]
    have h3 : ∀ a ∈ Finset.range n,
        ∑ b ∈ Finset.range (n + 1), (if a < b then b - a else 0)
          = (∑ b ∈ Finset.range n, (if a < b then b - a else 0)) + (n - a) := by
      intro a ha
      simp only [Finset.mem_range] at ha
      rw [Finset.sum_range_succ, if_pos ha]
    rw [h2, add_zero, Finset.sum_congr rfl h3, Finset.sum_add_distrib, ih, sum_range_sub,
      Nat.choose_succ_succ (n + 1) 2]
    norm_num
    omega

/-- **Wiener index of the path graph**: `W(P_n) = C(n+1, 3)`. -/
theorem wiener_path_formula (n : ℕ) :
    wienerIndex (SimpleGraph.pathGraph n) = (n + 1).choose 3 := by
  rw [← double_sum_eq n]
  rw [wienerIndex, Finset.sum_filter, Fintype.sum_prod_type]
  rw [← Fin.sum_univ_eq_sum_range (fun a => ∑ b ∈ Finset.range n, (if a < b then b - a else 0)) n]
  refine Finset.sum_congr rfl ?_
  intro a _
  rw [← Fin.sum_univ_eq_sum_range (fun b => (if (a : ℕ) < b then b - (a : ℕ) else 0)) n]
  refine Finset.sum_congr rfl ?_
  intro b _
  by_cases hab : (a : ℕ) < (b : ℕ)
  · simp only [hab, if_true, Fin.lt_def]
    exact pathGraph_dist_of_le a b (le_of_lt hab)
  · simp [Fin.lt_def, hab]

end Chem

