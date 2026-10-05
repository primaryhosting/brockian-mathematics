import Mathlib

/-!
# Wiener Path Formula
Category: Chemistry
Target: Chem.wiener_path_formula
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open SimpleGraph Finset

namespace Chem

/-- The Wiener index of a finite graph: the sum of the distances `d(u,v)` over all
unordered pairs `{u, v}` of vertices (the diagonal pairs contribute `0`). -/
noncomputable def wienerIndex {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : ℕ :=
  ∑ e : Sym2 V, Sym2.lift ⟨G.dist, fun _ _ => G.dist_comm⟩ e

/-- On a linearly ordered vertex set, the Wiener index is the sum of `d(u,v)` over the
ordered pairs `u < v`. -/
theorem wienerIndex_eq_sum_lt {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) :
    wienerIndex G = ∑ p ∈ Finset.univ.offDiag with p.1 < p.2, G.dist p.1 p.2 := by
  set f : Sym2 V → ℕ := Sym2.lift ⟨G.dist, fun _ _ => G.dist_comm⟩ with hf
  have hdiag : ∀ e : Sym2 V, e.IsDiag → f e = 0 := by
    intro e he
    induction e using Sym2.ind with
    | _ a b =>
      simp only [Sym2.mk_isDiag_iff] at he
      subst he
      simp [hf]
  have h1 : wienerIndex G = ∑ e ∈ Finset.univ.sym2 with ¬ e.IsDiag, f e := by
    rw [wienerIndex, ← hf, ← Finset.sym2_univ]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ.sym2 (fun e => e.IsDiag) f]
    rw [Finset.sum_eq_zero (fun e he => hdiag e (Finset.mem_filter.1 he).2), zero_add]
  rw [h1, Finset.sum_sym2_filter_not_isDiag]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [hf, show Sym2.mk x = s(x.1, x.2) from rfl, Sym2.lift_mk]

/-! ### Distances in the path graph -/

/-- In the path graph `P n` there is a walk of length `|i - j|` between any two vertices. -/
theorem pathGraph_exists_walk {n : ℕ} : ∀ (d : ℕ) (i j : Fin n), ((i : ℤ) - (j : ℤ)).natAbs = d →
    ∃ p : (pathGraph n).Walk i j, p.length = d := by
  intro d
  induction d with
  | zero =>
    intro i j h
    have hij : i = j := Fin.ext (by omega)
    subst hij
    exact ⟨SimpleGraph.Walk.nil, rfl⟩
  | succ d ih =>
    intro i j h
    rcases (by omega : (j : ℕ) = (i : ℕ) + (d + 1) ∨ (i : ℕ) = (j : ℕ) + (d + 1)) with hc | hc
    · have hlt : (i : ℕ) + 1 < n := by omega
      set k : Fin n := ⟨(i : ℕ) + 1, hlt⟩ with hk
      have hadj : (pathGraph n).Adj i k := by
        rw [SimpleGraph.pathGraph_adj]; left; simp [hk]
      obtain ⟨p, hp⟩ := ih k j (by simp [hk]; omega)
      exact ⟨SimpleGraph.Walk.cons hadj p, by simp [hp]⟩
    · have hlt : (i : ℕ) - 1 < n := by omega
      set k : Fin n := ⟨(i : ℕ) - 1, hlt⟩ with hk
      have hadj : (pathGraph n).Adj i k := by
        rw [SimpleGraph.pathGraph_adj]; right; simp [hk]; omega
      obtain ⟨p, hp⟩ := ih k j (by simp [hk]; omega)
      exact ⟨SimpleGraph.Walk.cons hadj p, by simp [hp]⟩

/-- Every walk in the path graph is at least as long as the difference of its endpoints. -/
theorem pathGraph_le_walk_length {n : ℕ} {i j : Fin n} (p : (pathGraph n).Walk i j) :
    ((i : ℤ) - (j : ℤ)).natAbs ≤ p.length := by
  induction p with
  | nil => simp
  | cons h p ih =>
    rw [SimpleGraph.pathGraph_adj] at h
    simp only [SimpleGraph.Walk.length_cons]
    omega

/-- The distance between two vertices of the path graph `P n` is `|i - j|`. -/
theorem pathGraph_dist {n : ℕ} (i j : Fin n) :
    (pathGraph n).dist i j = ((i : ℤ) - (j : ℤ)).natAbs := by
  obtain ⟨p, hp⟩ := pathGraph_exists_walk _ i j rfl
  refine le_antisymm (hp ▸ SimpleGraph.dist_le p) ?_
  obtain ⟨q, hq⟩ := (SimpleGraph.Walk.reachable p).exists_walk_length_eq_dist
  exact hq ▸ pathGraph_le_walk_length q

/-! ### The arithmetic identities -/

theorem sum_range_sub (n : ℕ) : ∑ i ∈ range n, (n - i) = (n + 1).choose 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ']
    have hc : ∀ i ∈ range n, (n + 1 - (i + 1)) = n - i := by intro i _; omega
    rw [Finset.sum_congr rfl hc, ih]
    have h : (n + 1 + 1).choose 2 = (n + 1).choose 1 + (n + 1).choose 2 :=
      Nat.choose_succ_succ (n + 1) 1
    simp only [Nat.choose_one_right] at h
    omega

theorem sum_range_pairs (n : ℕ) :
    ∑ i ∈ range n, ∑ j ∈ range n, (if i < j then j - i else 0) = (n + 1).choose 3 := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have h2 : ∀ i ∈ range n, ∑ j ∈ range (n + 1), (if i < j then j - i else 0)
        = (∑ j ∈ range n, (if i < j then j - i else 0)) + (n - i) := by
      intro i hi
      rw [Finset.sum_range_succ]
      simp only [Finset.mem_range] at hi
      simp [hi]
    rw [Finset.sum_congr rfl h2, Finset.sum_add_distrib, ih, sum_range_sub]
    have h3 : ∑ j ∈ range (n + 1), (if n < j then j - n else 0) = 0 := by
      refine Finset.sum_eq_zero (fun j hj => ?_)
      simp only [Finset.mem_range] at hj
      simp only [ite_eq_right_iff]
      omega
    have h : (n + 1 + 1).choose 3 = (n + 1).choose 2 + (n + 1).choose 3 :=
      Nat.choose_succ_succ (n + 1) 2
    rw [h3, add_zero]
    omega

/-! ### The Wiener index of the path graph -/

/-- **Wiener path formula**: the Wiener index of the path graph `P n` on `n` vertices
equals `C(n + 1, 3)`. -/
theorem wiener_path_formula (n : ℕ) : wienerIndex (pathGraph n) = (n + 1).choose 3 := by
  rw [wienerIndex_eq_sum_lt]
  have hset : ((Finset.univ : Finset (Fin n)).offDiag.filter (fun p => p.1 < p.2))
      = (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 < p.2) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_univ, true_and]
    exact ⟨fun h => h.2, fun h => ⟨ne_of_lt h, h⟩⟩
  set g : ℕ → ℕ → ℕ := fun i j => if i < j then j - i else 0 with hg
  have key : ∀ x y : Fin n, (if x < y then (pathGraph n).dist x y else 0) = g (x : ℕ) (y : ℕ) := by
    intro x y
    by_cases h : x < y
    · have h' : (x : ℕ) < (y : ℕ) := h
      simp only [h, if_pos, hg, h', pathGraph_dist]
      omega
    · have h' : ¬ ((x : ℕ) < (y : ℕ)) := h
      simp [h, hg, h']
  rw [hset, Finset.sum_filter, Fintype.sum_prod_type]
  simp only [key]
  rw [Fin.sum_univ_eq_sum_range (fun i => ∑ y : Fin n, g i (y : ℕ)) n]
  rw [Finset.sum_congr rfl (fun i _ => Fin.sum_univ_eq_sum_range (fun j => g i j) n)]
  exact sum_range_pairs n

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

