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
noncomputable def wienerIndex {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ :=
  (∑ u : V, ∑ v : V, G.dist u v) / 2

/-! ### The distance in the path graph -/

/-- Any walk in the path graph between `u` and `v` is at least as long as `|u - v|`. -/
theorem natDist_le_walk_length {n : ℕ} {u v : Fin n} (p : (pathGraph n).Walk u v) :
    Nat.dist u.val v.val ≤ p.length := by
  induction p with
  | nil => simp [Nat.dist_self]
  | @cons a b c h p ih =>
      rw [SimpleGraph.pathGraph_adj] at h
      simp only [SimpleGraph.Walk.length_cons]
      unfold Nat.dist at ih ⊢
      omega

/-- Upper bound for the distance in the path graph, proved by induction on the gap. -/
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
theorem pathGraph_dist {n : ℕ} (u v : Fin n) :
    (pathGraph n).dist u v = Nat.dist u.val v.val := by
  have hle : (pathGraph n).dist u v ≤ Nat.dist u.val v.val := by
    rcases le_total u.val v.val with h | h
    · refine pathGraph_dist_le_of_add _ u v ?_
      unfold Nat.dist
      omega
    · rw [SimpleGraph.dist_comm, Nat.dist_comm]
      refine pathGraph_dist_le_of_add _ v u ?_
      unfold Nat.dist
      omega
  have hge : Nat.dist u.val v.val ≤ (pathGraph n).dist u v := by
    obtain ⟨p, hp⟩ := (SimpleGraph.pathGraph_preconnected n u v).exists_walk_length_eq_dist
    exact hp ▸ natDist_le_walk_length p
  omega

/-! ### The arithmetic -/

/-- `∑_{i < n} |i - n| = C(n+1, 2)`. -/
theorem sum_natDist_top (n : ℕ) :
    ∑ i ∈ range n, Nat.dist i n = Nat.choose (n + 1) 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have hstep : ∑ i ∈ range n, Nat.dist i (n + 1)
          = (∑ i ∈ range n, Nat.dist i n) + n := by
        have hcongr : ∀ i ∈ range n, Nat.dist i (n + 1) = Nat.dist i n + 1 := by
          intro i hi
          simp only [Finset.mem_range] at hi
          unfold Nat.dist
          omega
        rw [Finset.sum_congr rfl hcongr, Finset.sum_add_distrib, Finset.sum_const,
          Finset.card_range, smul_eq_mul, mul_one]
      have hlast : Nat.dist n (n + 1) = 1 := by unfold Nat.dist; omega
      have hc2 : Nat.choose (n + 1 + 1) 2 = Nat.choose (n + 1) 1 + Nat.choose (n + 1) 2 := rfl
      rw [hstep, ih, hlast]
      simp only [Nat.choose_one_right] at hc2
      omega

/-- `∑_{i,j < n} |i - j| = 2 · C(n+1, 3)`. -/
theorem double_sum_natDist (n : ℕ) :
    ∑ i ∈ range n, ∑ j ∈ range n, Nat.dist i j = 2 * Nat.choose (n + 1) 3 := by
  induction n with
  | zero => decide
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have h1 : ∀ i ∈ range n, ∑ j ∈ range (n + 1), Nat.dist i j
          = (∑ j ∈ range n, Nat.dist i j) + Nat.dist i n := fun i _ => Finset.sum_range_succ _ _
      have h2 : ∑ j ∈ range n, Nat.dist n j = ∑ j ∈ range n, Nat.dist j n :=
        Finset.sum_congr rfl fun j _ => Nat.dist_comm n j
      rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, ih, sum_natDist_top,
        Finset.sum_range_succ, Nat.dist_self, add_zero, h2, sum_natDist_top]
      have hc3 : Nat.choose (n + 1 + 1) 3 = Nat.choose (n + 1) 2 + Nat.choose (n + 1) 3 := rfl
      omega

/-! ### The Wiener index of a path -/

/-- **Wiener path formula**: the Wiener index of the path graph `P n` equals `C(n+1, 3)`. -/
theorem wiener_path_formula (n : ℕ) :
    wienerIndex (pathGraph n) = Nat.choose (n + 1) 3 := by
  have hrow : ∀ u : Fin n, ∑ v : Fin n, (pathGraph n).dist u v
      = ∑ j ∈ range n, Nat.dist u.val j := by
    intro u
    rw [← Fin.sum_univ_eq_sum_range (fun j => Nat.dist u.val j) n]
    exact Finset.sum_congr rfl fun v _ => pathGraph_dist u v
  have hsum : ∑ u : Fin n, ∑ v : Fin n, (pathGraph n).dist u v = 2 * Nat.choose (n + 1) 3 := by
    rw [Finset.sum_congr rfl fun u _ => hrow u,
      Fin.sum_univ_eq_sum_range (fun i => ∑ j ∈ range n, Nat.dist i j) n]
    exact double_sum_natDist n
  unfold wienerIndex
  rw [hsum]
  omega

/-! ### Sanity checks -/

/-- `P 3` has distances `1, 1, 2`, so its Wiener index is `4 = C(4,3)`. -/
example : wienerIndex (pathGraph 3) = 4 := by
  rw [wiener_path_formula]
  decide

/-- `P 5` has Wiener index `20 = C(6,3)`. -/
example : wienerIndex (pathGraph 5) = 20 := by
  rw [wiener_path_formula]
  decide

end Chem

