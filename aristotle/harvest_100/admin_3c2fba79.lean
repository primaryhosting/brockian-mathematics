import Mathlib

/-!
# Wiener Path Formula
Category: Chemistry
Target: Chem.wiener_path_formula
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Finset SimpleGraph

/-- The Wiener index of a finite graph: the sum of the distances over all unordered
pairs of vertices. -/
noncomputable def wienerIndex {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ :=
  (∑ u : V, ∑ v : V, G.dist u v) / 2

/-! ### Distances in the path graph -/

/-- Any walk in the path graph is at least as long as the gap between the indices of its
endpoints. -/
lemma gap_le_walk_length {n : ℕ} {u v : Fin n} (p : (pathGraph n).Walk u v) :
    (u : ℕ) - (v : ℕ) + ((v : ℕ) - (u : ℕ)) ≤ p.length := by
  induction p with
  | nil => simp
  | @cons a b c h p ih =>
    rw [pathGraph_adj] at h
    rw [SimpleGraph.Walk.length_cons]
    omega

/-- Between two vertices of the path graph whose indices differ by `d` there is a walk of
length `d`. -/
lemma exists_walk_length_eq {n : ℕ} :
    ∀ (d : ℕ) (i j : Fin n), (j : ℕ) = (i : ℕ) + d →
      ∃ p : (pathGraph n).Walk i j, p.length = d := by
  intro d
  induction d with
  | zero =>
    intro i j h
    have : i = j := Fin.ext (by omega)
    subst this
    exact ⟨SimpleGraph.Walk.nil, rfl⟩
  | succ d ih =>
    intro i j h
    have hj : (j : ℕ) < n := j.isLt
    have hlt : (i : ℕ) + 1 < n := by omega
    let k : Fin n := ⟨(i : ℕ) + 1, hlt⟩
    have hadj : (pathGraph n).Adj i k := pathGraph_adj.2 (Or.inl rfl)
    obtain ⟨p, hp⟩ := ih k j (by simp only [k]; omega)
    exact ⟨SimpleGraph.Walk.cons hadj p, by simp [hp]⟩

/-- Key intermediate lemma: the distance between two vertices of the path graph is the
absolute difference of their indices. -/
theorem pathGraph_dist {n : ℕ} (i j : Fin n) :
    (pathGraph n).dist i j = (i : ℕ) - (j : ℕ) + ((j : ℕ) - (i : ℕ)) := by
  apply le_antisymm
  · rcases le_total (i : ℕ) (j : ℕ) with h | h
    · obtain ⟨p, hp⟩ := exists_walk_length_eq ((j : ℕ) - (i : ℕ)) i j (by omega)
      have := SimpleGraph.dist_le p
      omega
    · obtain ⟨p, hp⟩ := exists_walk_length_eq ((i : ℕ) - (j : ℕ)) j i (by omega)
      have := SimpleGraph.dist_le p
      rw [SimpleGraph.dist_comm]
      omega
  · obtain ⟨p, hp⟩ := (pathGraph_preconnected n i j).exists_walk_length_eq_dist
    have := gap_le_walk_length p
    omega

/-! ### The combinatorial sum -/

/-- Gauss' sum, in the form needed below. -/
lemma two_mul_sum_gap (n : ℕ) : 2 * ∑ i ∈ range n, (n - i) = n * (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have h : ∑ i ∈ range n, (n + 1 - i) = ∑ i ∈ range n, ((n - i) + 1) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      simp only [Finset.mem_range] at hi
      omega
    rw [h, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range]
    have hr : (n + 1) * (n + 1 + 1) = n * (n + 1) + 2 * (n + 1) := by ring
    simp only [smul_eq_mul, mul_one]
    omega

/-- `2 * C(n+1, 2) = n * (n+1)`. -/
lemma two_mul_choose_two (n : ℕ) : 2 * (n + 1).choose 2 = n * (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.choose_succ_succ' (n + 1) 1]
    simp only [Nat.choose_one_right] at *
    ring_nf
    ring_nf at ih
    omega

/-- Key intermediate lemma: the sum of all pairwise distances (over ordered pairs) in the
path graph `P n` is `2 * C(n+1, 3)`. -/
theorem sum_dist_pathGraph (n : ℕ) :
    ∑ i ∈ range n, ∑ j ∈ range n, (i - j + (j - i)) = 2 * (n + 1).choose 3 := by
  induction n with
  | zero => simp [Nat.choose]
  | succ n ih =>
    have hinner : ∀ i ∈ range (n + 1),
        ∑ j ∈ range (n + 1), (i - j + (j - i)) =
          (∑ j ∈ range n, (i - j + (j - i))) + (i - n + (n - i)) := by
      intro i _
      rw [Finset.sum_range_succ]
    rw [Finset.sum_congr rfl hinner, Finset.sum_add_distrib, Finset.sum_range_succ
      (fun i => ∑ j ∈ range n, (i - j + (j - i)))]
    have h1 : ∑ j ∈ range n, (n - j + (j - n)) = ∑ j ∈ range n, (n - j) := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      simp only [Finset.mem_range] at hj
      omega
    have h2 : ∑ i ∈ range (n + 1), (i - n + (n - i)) = ∑ i ∈ range n, (n - i) := by
      rw [Finset.sum_range_succ]
      have : ∑ i ∈ range n, (i - n + (n - i)) = ∑ i ∈ range n, (n - i) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        simp only [Finset.mem_range] at hi
        omega
      omega
    rw [h1, h2, ih]
    have hg := two_mul_sum_gap n
    have hc : (n + 1 + 1).choose 3 = (n + 1).choose 3 + (n + 1).choose 2 := by
      rw [show (3 : ℕ) = 2 + 1 from rfl, Nat.choose_succ_succ' (n + 1) 2, Nat.add_comm]
    have hc2 := two_mul_choose_two n
    omega

/-- **The Wiener index of the path graph `P n` is `C(n+1, 3)`.** -/
theorem wiener_path_formula (n : ℕ) :
    wienerIndex (pathGraph n) = (n + 1).choose 3 := by
  have h : ∑ u : Fin n, ∑ v : Fin n, (pathGraph n).dist u v = 2 * (n + 1).choose 3 := by
    rw [← sum_dist_pathGraph n]
    simp only [pathGraph_dist]
    rw [Fin.sum_univ_eq_sum_range (fun i => ∑ v : Fin n, (i - (v : ℕ) + ((v : ℕ) - i))) n]
    refine Finset.sum_congr rfl ?_
    intro i _
    exact Fin.sum_univ_eq_sum_range (fun j => (i - j + (j - i))) n
  rw [wienerIndex, h]
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

