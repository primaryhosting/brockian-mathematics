/-
# Friendship Theorem
Category: Frontier — Fields Medal Work
Target: Frontier.friendship_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` before any module docstring, so the header above is a plain comment
-- and is repeated below as the module docstring.)
import Mathlib

/-!
# Friendship Theorem
Category: Frontier — Fields Medal Work
Target: Frontier.friendship_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open Finset SimpleGraph Matrix

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A *friendship graph*: any two distinct vertices have exactly one common neighbour
("every two people have exactly one common friend"). -/
def IsFriendshipGraph (G : SimpleGraph V) : Prop :=
  ∀ v w : V, v ≠ w → ∃! u : V, G.Adj v u ∧ G.Adj w u

/-- A *politician* is a vertex adjacent to every other vertex. -/
def IsPolitician (G : SimpleGraph V) (v : V) : Prop := ∀ w : V, w ≠ v → G.Adj v w

section Basic

omit [DecidableEq V] in
/-- In a friendship graph, two distinct vertices have exactly one common neighbour. -/
theorem card_commonNeighbors_eq_one (hG : IsFriendshipGraph G) {v w : V} (hvw : v ≠ w) :
    #{u ∈ univ | G.Adj v u ∧ G.Adj u w} = 1 := by
  obtain ⟨u, hu, huniq⟩ := hG v w hvw
  rw [Finset.card_eq_one]
  refine ⟨u, ?_⟩
  ext x
  simp only [mem_filter, mem_univ, true_and, mem_singleton]
  constructor
  · exact fun h => huniq x ⟨h.1, h.2.symm⟩
  · rintro rfl; exact ⟨hu.1, hu.2.symm⟩

variable {R : Type*} [Semiring R]

/-- Off-diagonal entries of the square of the adjacency matrix of a friendship graph are `1`:
there is exactly one walk of length two between two distinct vertices. -/
theorem adjMatrix_sq_apply_of_ne (hG : IsFriendshipGraph G) {v w : V} (hvw : v ≠ w) :
    (G.adjMatrix R ^ 2 : Matrix V V R) v w = 1 := by
  rw [sq, Matrix.mul_apply]
  simp only [adjMatrix_apply, ite_mul, one_mul, zero_mul, ← ite_and, sum_boole]
  rw [card_commonNeighbors_eq_one hG hvw]
  simp

/-- The number of length-3 walks between nonadjacent vertices is the degree of the source. -/
theorem adjMatrix_pow_three_apply_of_not_adj (hG : IsFriendshipGraph G) {v w : V}
    (hvw : ¬ G.Adj v w) : (G.adjMatrix R ^ 3 : Matrix V V R) v w = G.degree v := by
  rw [pow_succ', adjMatrix_mul_apply, degree, card_eq_sum_ones, Nat.cast_sum]
  refine sum_congr rfl fun x hx => ?_
  rw [adjMatrix_sq_apply_of_ne hG, Nat.cast_one]
  rintro rfl
  rw [mem_neighborFinset] at hx
  exact hvw hx

/-- Nonadjacent vertices of a friendship graph have the same degree. -/
theorem degree_eq_of_not_adj (hG : IsFriendshipGraph G) {v w : V} (hvw : ¬ G.Adj v w) :
    G.degree v = G.degree w := by
  rw [← Nat.cast_id (G.degree v), ← Nat.cast_id (G.degree w),
    ← adjMatrix_pow_three_apply_of_not_adj (R := ℕ) hG hvw,
    ← adjMatrix_pow_three_apply_of_not_adj (R := ℕ) hG fun h => hvw (G.symm h)]
  conv_lhs => rw [← transpose_adjMatrix (α := ℕ) (G := G)]
  simp only [pow_succ _ 2, sq, ← transpose_mul, transpose_apply]
  simp only [mul_assoc]

/-- The square of the adjacency matrix of a `d`-regular friendship graph has `d` on the
diagonal and `1` everywhere else. -/
theorem adjMatrix_sq_of_regular (hG : IsFriendshipGraph G) {d : ℕ}
    (hd : G.IsRegularOfDegree d) :
    (G.adjMatrix R ^ 2 : Matrix V V R) = of fun v w => if v = w then (d : R) else 1 := by
  ext v w
  by_cases h : v = w
  · subst h; rw [sq, adjMatrix_mul_self_apply_self, hd]; simp
  · rw [adjMatrix_sq_apply_of_ne hG h, of_apply, if_neg h]

end Basic

/-- A friendship graph with no politician is regular: nonadjacent vertices always have the
same degree, and without a politician any two vertices are linked by a chain of nonadjacent
pairs. -/
theorem exists_regular_of_no_politician [Nonempty V] (hG : IsFriendshipGraph G)
    (hnp : ¬ ∃ v, IsPolitician G v) : ∃ d : ℕ, G.IsRegularOfDegree d := by
  have v := Classical.arbitrary V
  refine ⟨G.degree v, fun x => ?_⟩
  by_cases hvx : G.Adj v x
  swap; · exact (degree_eq_of_not_adj hG hvx).symm
  simp only [IsPolitician, not_exists, not_forall] at hnp
  obtain ⟨w, hwv, hvw⟩ := hnp v
  obtain ⟨y, hyx, hxy⟩ := hnp x
  by_cases hxw : G.Adj x w
  swap; · rw [degree_eq_of_not_adj hG hvw]; exact degree_eq_of_not_adj hG hxw
  rw [degree_eq_of_not_adj hG hxy]
  by_cases hvy : G.Adj v y
  swap; · exact (degree_eq_of_not_adj hG hvy).symm
  rw [degree_eq_of_not_adj hG hvw]
  refine degree_eq_of_not_adj hG fun hcontra => ?_
  obtain ⟨a, -, huniq⟩ := hG v w (Ne.symm hwv)
  exact hyx (by rw [huniq y ⟨hvy, hcontra.symm⟩, huniq x ⟨hvx, hxw.symm⟩])

/-- A `d`-regular friendship graph has `d ^ 2 - d + 1` vertices. -/
theorem card_of_regular [Nonempty V] (hG : IsFriendshipGraph G) {d : ℕ}
    (hd : G.IsRegularOfDegree d) : d + (Fintype.card V - 1) = d * d := by
  have v := Classical.arbitrary V
  trans ((G.adjMatrix ℕ ^ 2) *ᵥ (fun _ => 1)) v
  · rw [adjMatrix_sq_of_regular hG hd, mulVec, dotProduct, ← insert_erase (mem_univ v)]
    simp only [sum_insert, mul_one, if_true, Nat.cast_id, mem_erase, not_true,
      Ne, not_false_iff, add_right_inj, false_and, of_apply]
    rw [Finset.sum_const_nat, card_erase_of_mem (mem_univ v), mul_one]
    · rfl
    · intro x hx; simp [(ne_of_mem_erase hx).symm]
  · rw [sq, ← mulVec_mulVec]
    simp only [adjMatrix_mulVec_const_apply_of_regular hd, neighborFinset,
      card_neighborSet_eq_degree, hd v, Function.const_def, adjMatrix_mulVec_apply _ _ (mulVec _ _),
      mul_one, sum_const, Set.toFinset_card, smul_eq_mul, Nat.cast_id]

/-- A `d`-regular friendship graph with `d ≤ 1` has at most one vertex. -/
theorem exists_politician_of_degree_le_one [Nonempty V] (hG : IsFriendshipGraph G) {d : ℕ}
    (hd : G.IsRegularOfDegree d) (hd1 : d ≤ 1) : ∃ v, IsPolitician G v := by
  have hsq : d * d = d := by interval_cases d <;> norm_num
  have h := card_of_regular hG hd
  rw [hsq] at h
  have hcard : Fintype.card V ≤ 1 := by
    cases hn : Fintype.card V with
    | zero => exact Nat.zero_le _
    | succ n => omega
  refine ⟨Classical.arbitrary V, fun w hw => absurd (Fintype.card_le_one_iff.mp hcard _ _) hw⟩

/-- A `2`-regular friendship graph has three vertices, hence is complete. -/
theorem neighborFinset_eq_of_degree_eq_two [Nonempty V] (hG : IsFriendshipGraph G)
    (hd : G.IsRegularOfDegree 2) (v : V) : G.neighborFinset v = Finset.univ.erase v := by
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    rw [mem_neighborFinset] at hx
    exact Finset.mem_erase.mpr ⟨(G.ne_of_adj hx).symm, Finset.mem_univ _⟩
  · have hfr := card_of_regular hG hd
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), card_univ]
    have : G.degree v = 2 := hd v
    rw [card_neighborFinset_eq_degree, this]
    omega

/-- A `d`-regular friendship graph with `d ≤ 2` has a politician. -/
theorem exists_politician_of_degree_le_two [Nonempty V] (hG : IsFriendshipGraph G) {d : ℕ}
    (hd : G.IsRegularOfDegree d) (hle : d ≤ 2) : ∃ v, IsPolitician G v := by
  interval_cases d
  · exact exists_politician_of_degree_le_one hG hd (by norm_num)
  · exact exists_politician_of_degree_le_one hG hd (by norm_num)
  · refine ⟨Classical.arbitrary V, fun w hw => ?_⟩
    rw [← mem_neighborFinset, neighborFinset_eq_of_degree_eq_two hG hd]
    exact Finset.mem_erase.mpr ⟨hw, Finset.mem_univ _⟩

section ModP

variable {p : ℕ} {d : ℕ}

/-- Modulo a factor of `d - 1`, the square of the adjacency matrix of a `d`-regular friendship
graph is the all-ones matrix. -/
theorem adjMatrix_sq_mod_p_of_regular (hG : IsFriendshipGraph G) (dmod : (d : ZMod p) = 1)
    (hd : G.IsRegularOfDegree d) : G.adjMatrix (ZMod p) ^ 2 = of fun _ _ => 1 := by
  simp [adjMatrix_sq_of_regular hG hd, dmod]

omit [DecidableEq V] in
theorem adjMatrix_mul_const_one_of_regular (hd : G.IsRegularOfDegree d) {R : Type*} [Semiring R] :
    G.adjMatrix R * of (fun _ _ => 1) = of (fun _ _ => (d : R)) := by
  ext x y
  simp only [← hd x, degree, adjMatrix_mul_apply, sum_const, Nat.smul_one_eq_cast, of_apply]

omit [DecidableEq V] in
theorem adjMatrix_mul_const_one_mod_p_of_regular (dmod : (d : ZMod p) = 1)
    (hd : G.IsRegularOfDegree d) :
    G.adjMatrix (ZMod p) * of (fun _ _ => 1) = of (fun _ _ => 1) := by
  rw [adjMatrix_mul_const_one_of_regular hd, dmod]

/-- All powers `≥ 2` of the adjacency matrix reduce to the all-ones matrix mod `p`. -/
theorem adjMatrix_pow_mod_p_of_regular (hG : IsFriendshipGraph G) (dmod : (d : ZMod p) = 1)
    (hd : G.IsRegularOfDegree d) {k : ℕ} (hk : 2 ≤ k) :
    G.adjMatrix (ZMod p) ^ k = of (fun _ _ => 1) := by
  match k with
  | 0 | 1 => omega
  | k + 2 =>
    induction k with
    | zero => exact adjMatrix_sq_mod_p_of_regular hG dmod hd
    | succ k hind =>
      rw [pow_succ', hind (Nat.le_add_left 2 k)]
      exact adjMatrix_mul_const_one_mod_p_of_regular dmod hd

/-- The number of vertices of a `d`-regular friendship graph is `1` mod any factor of `d - 1`. -/
theorem card_mod_p_of_regular [Nonempty V] (hG : IsFriendshipGraph G) (dmod : (d : ZMod p) = 1)
    (hd : G.IsRegularOfDegree d) : (Fintype.card V : ZMod p) = 1 := by
  have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr inferInstance
  rw [← Nat.succ_pred_eq_of_pos hpos, Nat.succ_eq_add_one, Nat.pred_eq_sub_one]
  simp only [add_eq_right, Nat.cast_add, Nat.cast_one]
  have h := congr_arg (fun n : ℕ => (n : ZMod p)) (card_of_regular hG hd)
  revert h; simp [dmod]

end ModP

/-- There is no `d`-regular friendship graph with `3 ≤ d`: taking `p` a prime factor of `d - 1`,
the `p`-th power of the adjacency matrix over `ZMod p` has trace `1`, while the trace of the
adjacency matrix itself is `0`, so by Frobenius the trace of the `p`-th power is `0`. -/
theorem not_regular_of_three_le [Nonempty V] (hG : IsFriendshipGraph G) {d : ℕ}
    (hd : G.IsRegularOfDegree d) (h3 : 3 ≤ d) : False := by
  let p : ℕ := (d - 1).minFac
  have p_dvd_d_pred := (ZMod.natCast_eq_zero_iff _ _).mpr (d - 1).minFac_dvd
  have dpos : 1 ≤ d := by omega
  haveI : Fact p.Prime := ⟨Nat.minFac_prime (by omega)⟩
  have hp2 : 2 ≤ p := (Fact.out (p := p.Prime)).two_le
  have dmod : (d : ZMod p) = 1 := by
    rw [← Nat.succ_pred_eq_of_pos dpos, Nat.succ_eq_add_one, Nat.pred_eq_sub_one]
    simp only [add_eq_right, Nat.cast_add, Nat.cast_one]
    exact p_dvd_d_pred
  have Vmod := card_mod_p_of_regular hG dmod hd
  have htr := ZMod.trace_pow_card (G.adjMatrix (ZMod p))
  contrapose! htr; clear htr
  rw [trace_adjMatrix, zero_pow (Fact.out (p := p.Prime)).ne_zero]
  rw [adjMatrix_pow_mod_p_of_regular hG dmod hd hp2]
  dsimp only [Fintype.card] at Vmod
  simp only [Matrix.trace, Matrix.diag, mul_one, nsmul_eq_mul, sum_const, of_apply, Ne]
  rw [Vmod, ← Nat.cast_one (R := ZMod (Nat.minFac (d - 1))), ZMod.natCast_eq_zero_iff,
    Nat.dvd_one, Nat.minFac_eq_one_iff]
  omega

/-- **The friendship theorem** (Erdős–Rényi–Sós): in a finite (nonempty) graph in which every
two distinct vertices have exactly one common neighbour, there is a vertex adjacent to all
others. -/
theorem friendship_theorem [Nonempty V] (hG : IsFriendshipGraph G) :
    ∃ v : V, ∀ w : V, w ≠ v → G.Adj v w := by
  by_contra hnp
  obtain ⟨d, hd⟩ := exists_regular_of_no_politician hG hnp
  rcases lt_or_ge d 3 with h | h
  · exact hnp (exists_politician_of_degree_le_two hG hd (by omega))
  · exact not_regular_of_three_le hG hd h

/-- Sanity check that the hypothesis of the friendship theorem is satisfiable: the triangle is
a friendship graph. (Its three vertices are all politicians.) -/
theorem isFriendshipGraph_triangle : IsFriendshipGraph (⊤ : SimpleGraph (Fin 3)) := by
  simp only [IsFriendshipGraph, SimpleGraph.top_adj, ExistsUnique]
  decide

end Frontier

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

