/-
# Wiener Path Formula
Category: Chemistry
Target: Chem.wiener_path_formula
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Nat

set_option maxHeartbeats 1000000

namespace Chem

open SimpleGraph Finset

/-- The Wiener index of a finite graph: the sum of the graph distances over all
unordered pairs of vertices (equivalently, half the sum over all ordered pairs). -/
noncomputable def wienerIndex {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ :=
  (∑ u : V, ∑ v : V, G.dist u v) / 2

/-! ### Distances in the path graph -/

/-- Any walk in the path graph between `i` and `j` has length at least `|i - j|`. -/
lemma natDist_le_walk_length {n : ℕ} {i j : Fin n}
    (w : (pathGraph n).Walk i j) : Nat.dist i.val j.val ≤ w.length := by
  induction w with
  | nil => simp [Nat.dist_self]
  | @cons u v x h p ih =>
      have h1 : Nat.dist u.val v.val = 1 := by
        rw [pathGraph_adj] at h
        simp only [Nat.dist]
        omega
      have h2 : Nat.dist u.val x.val ≤ Nat.dist u.val v.val + Nat.dist v.val x.val :=
        Nat.dist.triangle_inequality _ _ _
      simp only [SimpleGraph.Walk.length_cons]
      omega

/-- In the path graph there is a walk of length at most `k` between `i` and `j`
whenever `|i - j| ≤ k`. -/
lemma exists_walk_length_le {n : ℕ} :
    ∀ (k : ℕ) (i j : Fin n), Nat.dist i.val j.val ≤ k →
      ∃ w : (pathGraph n).Walk i j, w.length ≤ k := by
  intro k
  induction k with
  | zero =>
      intro i j hij
      have : i = j := by
        apply Fin.ext
        simp only [Nat.dist] at hij
        omega
      subst this
      exact ⟨SimpleGraph.Walk.nil, by simp⟩
  | succ k ih =>
      intro i j hij
      rcases lt_trichotomy i.val j.val with h | h | h
      · have hlt : i.val + 1 < n := lt_of_le_of_lt h j.isLt
        refine ⟨SimpleGraph.Walk.cons (u := i) (v := ⟨i.val + 1, hlt⟩) ?_ ?_, ?_⟩
        · rw [pathGraph_adj]; exact Or.inl rfl
        · exact (ih ⟨i.val + 1, hlt⟩ j (by simp only [Nat.dist] at hij ⊢; omega)).choose
        · have := (ih ⟨i.val + 1, hlt⟩ j (by simp only [Nat.dist] at hij ⊢; omega)).choose_spec
          simpa [SimpleGraph.Walk.length_cons] using this
      · have : i = j := Fin.ext h
        subst this
        exact ⟨SimpleGraph.Walk.nil, by simp⟩
      · have hlt : i.val - 1 < n := lt_of_le_of_lt (Nat.sub_le _ _) i.isLt
        refine ⟨SimpleGraph.Walk.cons (u := i) (v := ⟨i.val - 1, hlt⟩) ?_ ?_, ?_⟩
        · rw [pathGraph_adj]; right; simp only; omega
        · exact (ih ⟨i.val - 1, hlt⟩ j (by simp only [Nat.dist] at hij ⊢; omega)).choose
        · have := (ih ⟨i.val - 1, hlt⟩ j (by simp only [Nat.dist] at hij ⊢; omega)).choose_spec
          simpa [SimpleGraph.Walk.length_cons] using this

/-- The distance between vertices `i` and `j` of the path graph `P n` is `|i - j|`. -/
theorem pathGraph_dist {n : ℕ} (i j : Fin n) :
    (pathGraph n).dist i j = Nat.dist i.val j.val := by
  refine le_antisymm ?_ ?_
  · obtain ⟨w, hw⟩ := exists_walk_length_le (Nat.dist i.val j.val) i j le_rfl
    exact le_trans (SimpleGraph.dist_le w) hw
  · obtain ⟨w, hw⟩ := exists_walk_length_le (Nat.dist i.val j.val) i j le_rfl
    have hr : (pathGraph n).Reachable i j := ⟨w⟩
    obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_dist
    rw [← hp]
    exact natDist_le_walk_length p

/-! ### The combinatorial sum -/

lemma sum_dist_to_top (n : ℕ) :
    ∑ i ∈ Finset.range n, Nat.dist i n = ∑ i ∈ Finset.range n, (i + 1) := by
  rw [← Finset.sum_range_reflect (fun i => i + 1) n]
  refine Finset.sum_congr rfl ?_
  intro i hi
  simp only [Finset.mem_range] at hi
  simp only [Nat.dist]
  omega

lemma two_mul_sum_succ (n : ℕ) :
    2 * ∑ i ∈ Finset.range n, (i + 1) = n * (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, Nat.mul_add, ih]
      ring

lemma two_mul_sum_dist_to_top (n : ℕ) :
    2 * ∑ i ∈ Finset.range n, Nat.dist i n = n * (n + 1) := by
  rw [sum_dist_to_top, two_mul_sum_succ]

lemma two_mul_choose_two (n : ℕ) : 2 * (n + 1).choose 2 = n * (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.choose_succ_succ (n + 1) 1, Nat.choose_one_right, Nat.mul_add, ih]
      ring

/-- The sum of `|i - j|` over all ordered pairs from `{0, …, n-1}` is `2 * C(n+1, 3)`. -/
lemma sum_sum_natDist (n : ℕ) :
    ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, Nat.dist i j = 2 * (n + 1).choose 3 := by
  induction n with
  | zero => simp [Nat.choose]
  | succ n ih =>
      have hinner : ∀ i : ℕ, ∑ j ∈ Finset.range (n + 1), Nat.dist i j
          = (∑ j ∈ Finset.range n, Nat.dist i j) + Nat.dist i n :=
        fun i => Finset.sum_range_succ _ _
      rw [Finset.sum_range_succ]
      simp only [hinner]
      rw [Finset.sum_add_distrib, ih, Nat.dist_self]
      have hswap : ∑ j ∈ Finset.range n, Nat.dist n j
          = ∑ j ∈ Finset.range n, Nat.dist j n :=
        Finset.sum_congr rfl fun j _ => Nat.dist_comm n j
      rw [hswap]
      have h2 := two_mul_sum_dist_to_top n
      have h3 : (n + 1 + 1).choose 3 = (n + 1).choose 2 + (n + 1).choose 3 :=
        Nat.choose_succ_succ (n + 1) 2
      have h4 := two_mul_choose_two n
      omega

/-! ### The Wiener index of the path graph -/

/-- **Wiener path formula**: the Wiener index of the path graph `P n` on `n` vertices
equals `C(n+1, 3)`. -/
theorem wiener_path_formula (n : ℕ) :
    wienerIndex (pathGraph n) = (n + 1).choose 3 := by
  have hsum : ∑ i : Fin n, ∑ j : Fin n, (pathGraph n).dist i j = 2 * (n + 1).choose 3 := by
    have h1 : ∀ i : Fin n, ∑ j : Fin n, (pathGraph n).dist i j
        = ∑ j ∈ Finset.range n, Nat.dist i.val j := by
      intro i
      rw [← Fin.sum_univ_eq_sum_range (fun j => Nat.dist i.val j) n]
      exact Finset.sum_congr rfl fun j _ => pathGraph_dist i j
    rw [Finset.sum_congr rfl fun i _ => h1 i,
      Fin.sum_univ_eq_sum_range (fun i => ∑ j ∈ Finset.range n, Nat.dist i j) n]
    exact sum_sum_natDist n
  unfold wienerIndex
  rw [hsum, Nat.mul_div_cancel_left _ (by norm_num)]

end Chem

