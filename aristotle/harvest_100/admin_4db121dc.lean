/-
# Friendship Theorem
Category: Frontier — Fields Medal Work
Target: Frontier.friendship_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above is a plain block comment rather than a `/-!` module docstring, since Lean
-- requires `import` to be the first command in a file.)

import Mathlib

/-!
## Notes on provenance of the argument

The statement below is the Erdős–Rényi–Sós friendship theorem.  Mathlib contains a proof of
it in its *Archive* (not in the main library): `Theorems100.friendship_theorem` in
`Archive/Wiedijk100Theorems/FriendshipGraphs.lean`, due to Aaron Anderson, Jalex Stark and
Kyle Miller (Apache 2.0).  Since the Archive is not part of the `Mathlib` library that this
project imports, the development is reproduced here, adapted into the `Frontier` namespace,
so that `Frontier.friendship_theorem` is self-contained on top of `Mathlib`.

The proof runs through adjacency matrices:
* nonadjacent vertices of a friendship graph have equal degree;
* hence a friendship graph with no "politician" (a vertex adjacent to all others) is regular;
* a `d`-regular friendship graph has `d ^ 2 - d + 1` vertices;
* for `d ≤ 2` one exhibits a politician directly;
* for `3 ≤ d`, taking a prime `p ∣ d - 1`, the adjacency matrix over `ZMod p` has trace `0`
  but its `p`-th power has trace `1`, contradicting `ZMod.trace_pow_card`.
-/

open scoped BigOperators
open scoped Classical

namespace Frontier

noncomputable section

open Finset SimpleGraph Matrix

universe u v

variable {V : Type u} {R : Type v} [Semiring R]

section FriendshipDef

variable (G : SimpleGraph V)

/-- A graph is a *friendship graph* when every pair of distinct vertices has exactly one
common neighbour. -/
def Friendship [Fintype V] : Prop :=
  ∀ ⦃v w : V⦄, v ≠ w → Fintype.card (G.commonNeighbors v w) = 1

/-- A *politician* is a vertex adjacent to every other vertex. -/
def ExistsPolitician : Prop :=
  ∃ v : V, ∀ w : V, v ≠ w → G.Adj v w

end FriendshipDef

variable [Fintype V] {G : SimpleGraph V} {d : ℕ} (hG : Friendship G)

namespace Friendship

variable (R)

include hG in
/-- In a friendship graph there is exactly one walk of length `2` between distinct vertices, so
the off-diagonal entries of the square of the adjacency matrix are all `1`. -/
theorem adjMatrix_sq_of_ne {v w : V} (hvw : v ≠ w) :
    (G.adjMatrix R ^ 2 : Matrix V V R) v w = 1 := by
  rw [sq, ← Nat.cast_one, ← hG hvw]
  simp only [mul_adjMatrix_apply, neighborFinset_eq_filter, adjMatrix_apply,
    sum_boole, filter_filter, and_comm, commonNeighbors,
    Fintype.card_ofFinset (s := filter (fun x ↦ x ∈ G.neighborSet v ∩ G.neighborSet w) univ),
    Set.mem_inter_iff, mem_neighborSet]

include hG in
/-- Counting length `3` walks between nonadjacent vertices. -/
theorem adjMatrix_pow_three_of_not_adj {v w : V} (non_adj : ¬G.Adj v w) :
    (G.adjMatrix R ^ 3 : Matrix V V R) v w = degree G v := by
  rw [pow_succ', adjMatrix_mul_apply, degree, card_eq_sum_ones, Nat.cast_sum]
  apply sum_congr rfl
  intro x hx
  rw [adjMatrix_sq_of_ne _ hG, Nat.cast_one]
  rintro ⟨rfl⟩
  rw [mem_neighborFinset] at hx
  exact non_adj hx

variable {R}

include hG in
/-- Nonadjacent vertices of a friendship graph have the same degree. -/
theorem degree_eq_of_not_adj {v w : V} (hvw : ¬G.Adj v w) : degree G v = degree G w := by
  rw [← Nat.cast_id (G.degree v), ← Nat.cast_id (G.degree w),
    ← adjMatrix_pow_three_of_not_adj ℕ hG hvw,
    ← adjMatrix_pow_three_of_not_adj ℕ hG fun h => hvw (G.symm h)]
  conv_lhs => rw [← transpose_adjMatrix]
  simp only [pow_succ _ 2, sq, ← transpose_mul, transpose_apply]
  simp only [mul_assoc]

include hG in
/-- The square of the adjacency matrix of a `d`-regular friendship graph. -/
theorem adjMatrix_sq_of_regular (hd : G.IsRegularOfDegree d) :
    G.adjMatrix R ^ 2 = of fun v w => if v = w then (d : R) else (1 : R) := by
  ext (v w); by_cases h : v = w
  · rw [h, sq, adjMatrix_mul_self_apply_self, hd]; simp
  · rw [adjMatrix_sq_of_ne R hG h, of_apply, if_neg h]

include hG in
theorem adjMatrix_sq_mod_p_of_regular {p : ℕ} (dmod : (d : ZMod p) = 1)
    (hd : G.IsRegularOfDegree d) : G.adjMatrix (ZMod p) ^ 2 = of fun _ _ => 1 := by
  simp [adjMatrix_sq_of_regular hG hd, dmod]

section Nonempty

variable [Nonempty V]

include hG in
/-- A friendship graph without a politician is regular. -/
theorem isRegularOf_not_existsPolitician (hG' : ¬ExistsPolitician G) :
    ∃ d : ℕ, G.IsRegularOfDegree d := by
  have v := Classical.arbitrary V
  use G.degree v
  intro x
  by_cases hvx : G.Adj v x; swap; · exact (degree_eq_of_not_adj hG hvx).symm
  dsimp only [Frontier.ExistsPolitician] at hG'
  push_neg at hG'
  rcases hG' v with ⟨w, hvw', hvw⟩
  rcases hG' x with ⟨y, hxy', hxy⟩
  by_cases hxw : G.Adj x w
  swap; · rw [degree_eq_of_not_adj hG hvw]; exact degree_eq_of_not_adj hG hxw
  rw [degree_eq_of_not_adj hG hxy]
  by_cases hvy : G.Adj v y
  swap; · exact (degree_eq_of_not_adj hG hvy).symm
  rw [degree_eq_of_not_adj hG hvw]
  apply degree_eq_of_not_adj hG
  intro hcontra
  rcases Finset.card_eq_one.mp (hG hvw') with ⟨⟨a, ha⟩, h⟩
  have key : ∀ {x}, x ∈ G.commonNeighbors v w → x = a := by
    intro x hx
    have h' : ⟨x, hx⟩ ∈ (univ : Finset (G.commonNeighbors v w)) := mem_univ (Subtype.mk x hx)
    rw [h, mem_singleton] at h'
    injection h'
  apply hxy'
  rw [key ((mem_commonNeighbors G).mpr ⟨hvx, G.symm hxw⟩),
    key ((mem_commonNeighbors G).mpr ⟨hvy, G.symm hcontra⟩)]

include hG in
/-- A `d`-regular friendship graph has `d ^ 2 - d + 1` vertices. -/
theorem card_of_regular (hd : G.IsRegularOfDegree d) : d + (Fintype.card V - 1) = d * d := by
  have v := Classical.arbitrary V
  trans ((G.adjMatrix ℕ ^ 2) *ᵥ (fun _ => 1)) v
  · rw [adjMatrix_sq_of_regular hG hd, mulVec, dotProduct, ← insert_erase (mem_univ v)]
    simp only [sum_insert, mul_one, if_true, Nat.cast_id, mem_erase, not_true,
      Ne, not_false_iff, add_right_inj, false_and, of_apply]
    rw [Finset.sum_const_nat, card_erase_of_mem (mem_univ v), mul_one]; · rfl
    intro x hx; simp [(ne_of_mem_erase hx).symm]
  · rw [sq, ← mulVec_mulVec]
    simp only [adjMatrix_mulVec_const_apply_of_regular hd, neighborFinset,
      card_neighborSet_eq_degree, hd v, Function.const_def, adjMatrix_mulVec_apply _ _ (mulVec _ _),
      mul_one, sum_const, Set.toFinset_card, smul_eq_mul, Nat.cast_id]

include hG in
/-- The size of a `d`-regular friendship graph is `1` modulo any factor `p ∣ d - 1`. -/
theorem card_mod_p_of_regular {p : ℕ} (dmod : (d : ZMod p) = 1) (hd : G.IsRegularOfDegree d) :
    (Fintype.card V : ZMod p) = 1 := by
  have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr inferInstance
  rw [← Nat.succ_pred_eq_of_pos hpos, Nat.succ_eq_add_one, Nat.pred_eq_sub_one]
  simp only [add_eq_right, Nat.cast_add, Nat.cast_one]
  have h := congr_arg (fun n : ℕ => (n : ZMod p)) (card_of_regular hG hd)
  revert h; simp [dmod]

end Nonempty

theorem adjMatrix_sq_mul_const_one_of_regular (hd : G.IsRegularOfDegree d) :
    G.adjMatrix R * of (fun _ _ => 1) = of (fun _ _ => (d : R)) := by
  ext x
  simp only [← hd x, degree, adjMatrix_mul_apply, sum_const, Nat.smul_one_eq_cast, of_apply]

theorem adjMatrix_mul_const_one_mod_p_of_regular {p : ℕ} (dmod : (d : ZMod p) = 1)
    (hd : G.IsRegularOfDegree d) :
    G.adjMatrix (ZMod p) * of (fun _ _ => 1) = of (fun _ _ => 1) := by
  rw [adjMatrix_sq_mul_const_one_of_regular hd, dmod]

include hG in
/-- Modulo a factor of `d - 1`, all powers `≥ 2` of the adjacency matrix of a `d`-regular
friendship graph are the all-ones matrix. -/
theorem adjMatrix_pow_mod_p_of_regular {p : ℕ} (dmod : (d : ZMod p) = 1)
    (hd : G.IsRegularOfDegree d) {k : ℕ} (hk : 2 ≤ k) :
    G.adjMatrix (ZMod p) ^ k = of (fun _ _ => 1) := by
  match k with
  | 0 | 1 => exfalso; omega
  | k + 2 =>
    induction k with
    | zero => exact adjMatrix_sq_mod_p_of_regular hG dmod hd
    | succ k hind =>
      rw [pow_succ', hind (Nat.le_add_left 2 k)]
      exact adjMatrix_mul_const_one_mod_p_of_regular dmod hd

variable [Nonempty V]

include hG in
/-- A `d`-regular friendship graph with `3 ≤ d` cannot exist: a trace computation modulo a
prime factor of `d - 1` gives `0 = 1`. -/
theorem false_of_three_le_degree (hd : G.IsRegularOfDegree d) (h : 3 ≤ d) : False := by
  -- get a prime factor of `d - 1`
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
  -- now we reduce to a trace calculation
  have := ZMod.trace_pow_card (G.adjMatrix (ZMod p))
  contrapose! this; clear this
  -- the trace is `0` mod `p` when computed one way
  rw [trace_adjMatrix, zero_pow this.out.ne_zero]
  -- but the trace is `1` mod `p` when computed the other way
  rw [adjMatrix_pow_mod_p_of_regular hG dmod hd hp2]
  dsimp only [Fintype.card] at Vmod
  simp only [Matrix.trace, Matrix.diag, mul_one, nsmul_eq_mul, sum_const, of_apply, Ne]
  rw [Vmod, ← Nat.cast_one (R := ZMod (Nat.minFac (d - 1))), ZMod.natCast_eq_zero_iff,
    Nat.dvd_one, Nat.minFac_eq_one_iff]
  omega

include hG in
/-- If `d ≤ 1`, a `d`-regular friendship graph has at most one vertex. -/
theorem existsPolitician_of_degree_le_one (hd : G.IsRegularOfDegree d) (hd1 : d ≤ 1) :
    ExistsPolitician G := by
  have sq : d * d = d := by interval_cases d <;> norm_num
  have h := card_of_regular hG hd
  rw [sq] at h
  have : Fintype.card V ≤ 1 := by
    cases hn : Fintype.card V with
    | zero => exact zero_le _
    | succ n => omega
  use Classical.arbitrary V
  intro w h; exfalso
  apply h
  apply Fintype.card_le_one_iff.mp this

include hG in
/-- If `d = 2`, a `d`-regular friendship graph is the triangle. -/
theorem neighborFinset_eq_of_degree_eq_two (hd : G.IsRegularOfDegree 2) (v : V) :
    G.neighborFinset v = Finset.univ.erase v := by
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

include hG in
theorem existsPolitician_of_degree_eq_two (hd : G.IsRegularOfDegree 2) : ExistsPolitician G := by
  have v := Classical.arbitrary V
  use v
  intro w hvw
  rw [← mem_neighborFinset, neighborFinset_eq_of_degree_eq_two hG hd v, Finset.mem_erase]
  exact ⟨hvw.symm, Finset.mem_univ _⟩

include hG in
theorem existsPolitician_of_degree_le_two (hd : G.IsRegularOfDegree d) (h : d ≤ 2) :
    ExistsPolitician G := by
  interval_cases d
  iterate 2 apply existsPolitician_of_degree_le_one hG hd; norm_num
  exact existsPolitician_of_degree_eq_two hG hd

end Friendship

include hG in
/-- **Friendship theorem** (Erdős–Rényi–Sós), in terms of the `Friendship` /
`ExistsPolitician` predicates: a finite nonempty friendship graph has a politician. -/
theorem existsPolitician_of_friendship [Nonempty V] : ExistsPolitician G := by
  by_contra npG
  rcases Friendship.isRegularOf_not_existsPolitician hG npG with ⟨d, dreg⟩
  rcases lt_or_ge d 3 with dle2 | dge3
  · exact npG (Friendship.existsPolitician_of_degree_le_two hG dreg (Nat.lt_succ_iff.mp dle2))
  · exact Friendship.false_of_three_le_degree hG dreg dge3

end

/-- **Friendship theorem** (Erdős–Rényi–Sós, 1966).

If `G` is a graph on a finite nonempty vertex set in which every two distinct people have
exactly one common friend, then someone is everyone's friend: there is a vertex adjacent to
all other vertices. -/
theorem friendship_theorem {V : Type u} [Fintype V] [Nonempty V] (G : SimpleGraph V)
    (hG : ∀ v w : V, v ≠ w → (G.commonNeighbors v w).ncard = 1) :
    ∃ v : V, ∀ w : V, v ≠ w → G.Adj v w := by
  have hG' : Friendship G := by
    intro v w hvw
    have h := hG v w hvw
    rwa [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card] at h
  exact existsPolitician_of_friendship hG'

end Frontier

