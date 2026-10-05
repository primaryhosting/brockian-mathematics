import Mathlib
-- (Lean requires `import` to precede any module docstring, so the header comment
-- requested for this file follows immediately below.)
/-!
# Friendship Theorem
Category: Frontier — Fields Medal Work
Target: Frontier.friendship_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
The **friendship theorem** of Erdős, Rényi and Sós: in a finite graph in which every two
distinct vertices have exactly one common neighbour, there is a vertex adjacent to all others.

The development below follows the classical adjacency-matrix proof:

* nonadjacent vertices have equal degrees (counting walks of length `3`);
* hence a friendship graph with no "politician" is `d`-regular;
* a `d`-regular friendship graph has `d ^ 2 - d + 1` vertices;
* the cases `d ≤ 2` produce a politician directly;
* for `3 ≤ d`, take a prime `p ∣ d - 1`; over `ZMod p` the `p`-th power of the adjacency
  matrix has trace `1`, while `trace (A ^ p) = (trace A) ^ p = 0`, a contradiction.
-/

namespace Frontier

noncomputable section

open Finset SimpleGraph Matrix

universe u v

variable {V : Type u} {R : Type v} [Semiring R] [Fintype V]

open scoped Classical in
/-- A graph is a *friendship graph* if any two distinct vertices have exactly one
common neighbour. -/
def Friendship (G : SimpleGraph V) : Prop :=
  ∀ ⦃v w : V⦄, v ≠ w → Fintype.card (G.commonNeighbors v w) = 1

/-- A *politician* is a vertex adjacent to every other vertex. -/
def ExistsPolitician (G : SimpleGraph V) : Prop :=
  ∃ v : V, ∀ w : V, v ≠ w → G.Adj v w

namespace Friendship

variable {G : SimpleGraph V} {d : ℕ}

open scoped Classical in
/-- In a friendship graph, all off-diagonal entries of the square of the adjacency matrix
are `1`: they count the (unique) common neighbours. -/
theorem adjMatrix_sq_of_ne (hG : Friendship G) (R) [Semiring R] {v w : V} (hvw : v ≠ w) :
    (G.adjMatrix R ^ 2 : Matrix V V R) v w = 1 := by
  rw [sq, ← Nat.cast_one, ← hG hvw]
  simp only [mul_adjMatrix_apply, neighborFinset_eq_filter, adjMatrix_apply,
    sum_boole, filter_filter, and_comm, commonNeighbors,
    Fintype.card_ofFinset (s := filter (fun x ↦ x ∈ G.neighborSet v ∩ G.neighborSet w) univ),
    Set.mem_inter_iff, mem_neighborSet]

open scoped Classical in
/-- Counting walks of length `3` between nonadjacent vertices. -/
theorem adjMatrix_pow_three_of_not_adj (hG : Friendship G) (R) [Semiring R] {v w : V}
    (hvw : ¬G.Adj v w) : (G.adjMatrix R ^ 3 : Matrix V V R) v w = G.degree v := by
  rw [pow_succ', adjMatrix_mul_apply, degree, card_eq_sum_ones, Nat.cast_sum]
  refine sum_congr rfl fun x hx => ?_
  rw [adjMatrix_sq_of_ne hG _, Nat.cast_one]
  rintro ⟨rfl⟩
  rw [mem_neighborFinset] at hx
  exact hvw hx

open scoped Classical in
/-- Nonadjacent vertices of a friendship graph have the same degree, since the adjacency
matrix is symmetric. -/
theorem degree_eq_of_not_adj (hG : Friendship G) {v w : V} (hvw : ¬G.Adj v w) :
    G.degree v = G.degree w := by
  rw [← Nat.cast_id (G.degree v), ← Nat.cast_id (G.degree w),
    ← adjMatrix_pow_three_of_not_adj hG ℕ hvw,
    ← adjMatrix_pow_three_of_not_adj hG ℕ fun h => hvw (G.symm h)]
  conv_lhs => rw [← transpose_adjMatrix]
  simp only [pow_succ _ 2, sq, ← transpose_mul, transpose_apply]
  simp only [mul_assoc]

open scoped Classical in
/-- For a `d`-regular friendship graph the square of the adjacency matrix is determined:
`d` on the diagonal, `1` off it. -/
theorem adjMatrix_sq_of_regular (hG : Friendship G) (R) [Semiring R]
    (hd : G.IsRegularOfDegree d) :
    G.adjMatrix R ^ 2 = of fun v w => if v = w then (d : R) else (1 : R) := by
  ext v w
  by_cases h : v = w
  · rw [h, sq, adjMatrix_mul_self_apply_self, hd]; simp
  · rw [adjMatrix_sq_of_ne hG R h, of_apply, if_neg h]

open scoped Classical in
theorem adjMatrix_sq_mod_p_of_regular (hG : Friendship G) {p : ℕ} (dmod : (d : ZMod p) = 1)
    (hd : G.IsRegularOfDegree d) : G.adjMatrix (ZMod p) ^ 2 = of fun _ _ => 1 := by
  simp [adjMatrix_sq_of_regular hG (ZMod p) hd, dmod]

section Nonempty

variable [Nonempty V]

open scoped Classical in
/-- A friendship graph without a politician is regular. -/
theorem isRegularOf_not_existsPolitician (hG : Friendship G) (hG' : ¬ExistsPolitician G) :
    ∃ d : ℕ, G.IsRegularOfDegree d := by
  have v := Classical.arbitrary V
  refine ⟨G.degree v, fun x => ?_⟩
  by_cases hvx : G.Adj v x; swap
  · exact (degree_eq_of_not_adj hG hvx).symm
  dsimp only [ExistsPolitician] at hG'
  push_neg at hG'
  obtain ⟨w, hvw', hvw⟩ := hG' v
  obtain ⟨y, hxy', hxy⟩ := hG' x
  by_cases hxw : G.Adj x w
  swap
  · rw [degree_eq_of_not_adj hG hvw]; exact degree_eq_of_not_adj hG hxw
  rw [degree_eq_of_not_adj hG hxy]
  by_cases hvy : G.Adj v y
  swap
  · exact (degree_eq_of_not_adj hG hvy).symm
  rw [degree_eq_of_not_adj hG hvw]
  refine degree_eq_of_not_adj hG fun hcontra => ?_
  obtain ⟨⟨a, ha⟩, h⟩ := Fintype.card_eq_one_iff.mp (hG hvw')
  have key : ∀ {x}, x ∈ G.commonNeighbors v w → x = a := by
    intro x hx
    exact congrArg Subtype.val (h ⟨x, hx⟩)
  exact hxy' (by
    rw [key ((mem_commonNeighbors G).mpr ⟨hvx, G.symm hxw⟩),
      key ((mem_commonNeighbors G).mpr ⟨hvy, G.symm hcontra⟩)])

open scoped Classical in
/-- A `d`-regular friendship graph has `d ^ 2 - d + 1` vertices. -/
theorem card_of_regular (hG : Friendship G) (hd : G.IsRegularOfDegree d) :
    d + (Fintype.card V - 1) = d * d := by
  have v := Classical.arbitrary V
  trans ((G.adjMatrix ℕ ^ 2) *ᵥ (fun _ => 1)) v
  · rw [adjMatrix_sq_of_regular hG ℕ hd, mulVec, dotProduct, ← insert_erase (mem_univ v)]
    simp only [sum_insert, mul_one, if_true, Nat.cast_id, mem_erase, not_true,
      Ne, not_false_iff, add_right_inj, false_and, of_apply]
    rw [Finset.sum_const_nat, card_erase_of_mem (mem_univ v), mul_one]
    · rfl
    · intro x hx; simp [(ne_of_mem_erase hx).symm]
  · rw [sq, ← mulVec_mulVec]
    simp only [adjMatrix_mulVec_const_apply_of_regular hd, neighborFinset,
      card_neighborSet_eq_degree, hd v, Function.const_def, adjMatrix_mulVec_apply _ _ (mulVec _ _),
      mul_one, sum_const, Set.toFinset_card, smul_eq_mul, Nat.cast_id]

open scoped Classical in
/-- The number of vertices of a `d`-regular friendship graph is `1` modulo any `p ∣ d - 1`. -/
theorem card_mod_p_of_regular (hG : Friendship G) {p : ℕ} (dmod : (d : ZMod p) = 1)
    (hd : G.IsRegularOfDegree d) : (Fintype.card V : ZMod p) = 1 := by
  have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr inferInstance
  rw [← Nat.succ_pred_eq_of_pos hpos, Nat.succ_eq_add_one, Nat.pred_eq_sub_one]
  simp only [add_eq_right, Nat.cast_add, Nat.cast_one]
  have h := congr_arg (fun n : ℕ => (n : ZMod p)) (card_of_regular hG hd)
  revert h; simp [dmod]

end Nonempty

open scoped Classical in
theorem adjMatrix_mul_const_one_of_regular (R) [Semiring R] (hd : G.IsRegularOfDegree d) :
    G.adjMatrix R * of (fun _ _ => 1) = of (fun _ _ => (d : R)) := by
  ext x
  simp only [← hd x, degree, adjMatrix_mul_apply, sum_const, Nat.smul_one_eq_cast, of_apply]

open scoped Classical in
theorem adjMatrix_mul_const_one_mod_p_of_regular {p : ℕ} (dmod : (d : ZMod p) = 1)
    (hd : G.IsRegularOfDegree d) :
    G.adjMatrix (ZMod p) * of (fun _ _ => 1) = of (fun _ _ => 1) := by
  rw [adjMatrix_mul_const_one_of_regular (ZMod p) hd, dmod]

open scoped Classical in
/-- Modulo a factor of `d - 1`, all powers `≥ 2` of the adjacency matrix of a `d`-regular
friendship graph are the all-ones matrix. -/
theorem adjMatrix_pow_mod_p_of_regular (hG : Friendship G) {p : ℕ} (dmod : (d : ZMod p) = 1)
    (hd : G.IsRegularOfDegree d) {k : ℕ} (hk : 2 ≤ k) :
    G.adjMatrix (ZMod p) ^ k = of (fun _ _ => 1) := by
  match k with
  | 0 | 1 => exact absurd hk (by omega)
  | k + 2 =>
    induction k with
    | zero => exact adjMatrix_sq_mod_p_of_regular hG dmod hd
    | succ k hind =>
      rw [pow_succ', hind (Nat.le_add_left 2 k)]
      exact adjMatrix_mul_const_one_mod_p_of_regular dmod hd

variable [Nonempty V]

open scoped Classical in
/-- The key step: a `d`-regular friendship graph with `3 ≤ d` cannot exist. -/
theorem false_of_three_le_degree (hG : Friendship G) (hd : G.IsRegularOfDegree d) (h : 3 ≤ d) :
    False := by
  set p : ℕ := (d - 1).minFac with hp
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
  rw [Vmod, ← Nat.cast_one (R := ZMod p), ZMod.natCast_eq_zero_iff, Nat.dvd_one, hp,
    Nat.minFac_eq_one_iff]
  omega

open scoped Classical in
/-- If `d ≤ 1`, a `d`-regular friendship graph has at most one vertex. -/
theorem existsPolitician_of_degree_le_one (hG : Friendship G) (hd : G.IsRegularOfDegree d)
    (hd1 : d ≤ 1) : ExistsPolitician G := by
  have hsq : d * d = d := by interval_cases d <;> norm_num
  have h := card_of_regular hG hd
  rw [hsq] at h
  have hcard : Fintype.card V ≤ 1 := by
    cases hn : Fintype.card V with
    | zero => exact Nat.zero_le _
    | succ n => omega
  refine ⟨Classical.arbitrary V, fun w hw => absurd (Fintype.card_le_one_iff.mp hcard _ _) hw⟩

open scoped Classical in
theorem neighborFinset_eq_of_degree_eq_two (hG : Friendship G) (hd : G.IsRegularOfDegree 2)
    (v : V) : G.neighborFinset v = Finset.univ.erase v := by
  apply Finset.eq_of_subset_of_card_le
  · rw [Finset.subset_iff]
    intro x
    rw [mem_neighborFinset, Finset.mem_erase]
    exact fun h => ⟨(G.ne_of_adj h).symm, Finset.mem_univ _⟩
  convert_to 2 ≤ _
  · convert_to _ = Fintype.card V - 1
    · have hfr := card_of_regular hG hd
      omega
    · exact Finset.card_erase_of_mem (Finset.mem_univ _)
  · dsimp only [IsRegularOfDegree, degree] at hd
    rw [hd]

open scoped Classical in
theorem existsPolitician_of_degree_eq_two (hG : Friendship G) (hd : G.IsRegularOfDegree 2) :
    ExistsPolitician G := by
  refine ⟨Classical.arbitrary V, fun w hvw => ?_⟩
  rw [← mem_neighborFinset, neighborFinset_eq_of_degree_eq_two hG hd, Finset.mem_erase]
  exact ⟨hvw.symm, Finset.mem_univ _⟩

open scoped Classical in
theorem existsPolitician_of_degree_le_two (hG : Friendship G) (hd : G.IsRegularOfDegree d)
    (h : d ≤ 2) : ExistsPolitician G := by
  interval_cases d
  iterate 2 exact existsPolitician_of_degree_le_one hG hd (by norm_num)
  exact existsPolitician_of_degree_eq_two hG hd

end Friendship

open scoped Classical in
/-- Every finite nonempty friendship graph has a politician. -/
theorem existsPolitician_of_friendship [Nonempty V] {G : SimpleGraph V} (hG : Friendship G) :
    ExistsPolitician G := by
  by_contra npG
  obtain ⟨d, dreg⟩ := hG.isRegularOf_not_existsPolitician npG
  rcases lt_or_ge d 3 with dle2 | dge3
  · exact npG (hG.existsPolitician_of_degree_le_two dreg (Nat.lt_succ_iff.mp dle2))
  · exact hG.false_of_three_le_degree dreg dge3

/-- **Friendship theorem** (Erdős–Rényi–Sós).  If in a finite nonempty graph every two
distinct people have exactly one common friend, then somebody is a friend of everybody
else. -/
theorem friendship_theorem {V : Type u} [Fintype V] [Nonempty V] {G : SimpleGraph V}
    (hG : ∀ v w : V, v ≠ w → ∃! u : V, G.Adj v u ∧ G.Adj w u) :
    ∃ v : V, ∀ w : V, v ≠ w → G.Adj v w := by
  classical
  refine existsPolitician_of_friendship (V := V) (G := G) ?_
  intro v w hvw
  obtain ⟨u, hu, huniq⟩ := hG v w hvw
  refine Fintype.card_eq_one_iff.mpr ⟨⟨u, (mem_commonNeighbors G).mpr hu⟩, fun y => ?_⟩
  exact Subtype.ext (huniq y.1 ((mem_commonNeighbors G).mp y.2))

end

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

