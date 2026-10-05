import Mathlib

/-!
# Friendship Theorem
Category: Frontier — Fields Medal Work
Target: Frontier.friendship_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
The Erdős–Rényi–Sós friendship theorem: in a finite graph in which every two distinct
vertices have exactly one common neighbour, there is a vertex adjacent to all others.

The proof follows the classical adjacency-matrix argument:
* the square of the adjacency matrix has all off-diagonal entries equal to `1`;
* non-adjacent vertices have equal degrees;
* without a politician the graph is regular, of some degree `d`;
* counting gives `d + (n - 1) = d * d` where `n` is the number of vertices;
* `d ≤ 2` forces a politician directly;
* for `d ≥ 3` one takes a prime `p ∣ d - 1` and computes the trace of the `p`-th power of
  the adjacency matrix over `ZMod p` in two ways, obtaining `0 = 1`.
-/

open Finset SimpleGraph Matrix

namespace Frontier

noncomputable section

open scoped Classical

universe u v

variable {V : Type u} {R : Type v} [Semiring R]

/-- The hypothesis of the friendship theorem: every pair of distinct vertices has exactly
one common neighbour. -/
def Friendship (G : SimpleGraph V) [Fintype V] : Prop :=
  ∀ ⦃v w : V⦄, v ≠ w → Fintype.card (G.commonNeighbors v w) = 1

/-- A *politician* is a vertex adjacent to every other vertex. -/
def ExistsPolitician (G : SimpleGraph V) : Prop :=
  ∃ v : V, ∀ w : V, v ≠ w → G.Adj v w

variable [Fintype V] {G : SimpleGraph V} {d : ℕ}

section Basic

/-- In a friendship graph, the off-diagonal entries of the square of the adjacency matrix
are all `1`: they count the (unique) length-two walks between distinct vertices. -/
theorem adjMatrix_sq_apply_of_ne (hG : Friendship G) (R : Type v) [Semiring R] {v w : V}
    (hvw : v ≠ w) : (G.adjMatrix R ^ 2 : Matrix V V R) v w = 1 := by
  have h1 : (G.adjMatrix R ^ 2 : Matrix V V R) v w
      = ((univ.filter fun u => G.Adj v u ∧ G.Adj u w).card : R) := by
    rw [sq, Matrix.mul_apply]
    simp only [adjMatrix_apply, ite_zero_mul_ite_zero, one_mul, Finset.sum_boole]
  have h2 : Fintype.card (G.commonNeighbors v w)
      = (univ.filter fun u => G.Adj v u ∧ G.Adj u w).card := by
    rw [← Set.toFinset_card]
    congr 1
    ext u
    simp [mem_commonNeighbors, adj_comm]
  rw [h1, ← h2, hG hvw, Nat.cast_one]

/-- The number of length-three walks from `v` to a non-neighbour `w` is the degree of `v`. -/
theorem adjMatrix_cube_apply_of_not_adj (hG : Friendship G) (R : Type v) [Semiring R] {v w : V}
    (hvw : ¬G.Adj v w) : (G.adjMatrix R ^ 3 : Matrix V V R) v w = G.degree v := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ', adjMatrix_mul_apply]
  have : ∀ u ∈ G.neighborFinset v, (G.adjMatrix R ^ 2 : Matrix V V R) u w = 1 := by
    intro u hu
    refine adjMatrix_sq_apply_of_ne hG R ?_
    rintro rfl
    exact hvw ((mem_neighborFinset _ _ _).1 hu)
  rw [Finset.sum_congr rfl this, Finset.sum_const, card_neighborFinset_eq_degree,
    nsmul_eq_mul, mul_one]

/-- Non-adjacent vertices of a friendship graph have the same degree. -/
theorem degree_eq_of_not_adj (hG : Friendship G) {v w : V} (hvw : ¬G.Adj v w) :
    G.degree v = G.degree w := by
  have hsymm : (G.adjMatrix ℕ ^ 3)ᵀ = G.adjMatrix ℕ ^ 3 := by
    rw [Matrix.transpose_pow, transpose_adjMatrix]
  have h1 : (G.adjMatrix ℕ ^ 3 : Matrix V V ℕ) v w = G.degree v :=
    adjMatrix_cube_apply_of_not_adj hG ℕ hvw
  have h2 : (G.adjMatrix ℕ ^ 3 : Matrix V V ℕ) w v = G.degree w :=
    adjMatrix_cube_apply_of_not_adj hG ℕ fun h => hvw h.symm
  rw [← h1, ← h2]
  exact congrFun (congrFun hsymm w) v

/-- The square of the adjacency matrix of a `d`-regular friendship graph. -/
theorem adjMatrix_sq_of_regular (hG : Friendship G) (hd : G.IsRegularOfDegree d) :
    G.adjMatrix R ^ 2 = Matrix.of fun v w => if v = w then (d : R) else (1 : R) := by
  ext v w
  by_cases h : v = w
  · subst h
    rw [sq, adjMatrix_mul_self_apply_self, hd v]
    simp
  · rw [adjMatrix_sq_apply_of_ne hG R h, Matrix.of_apply, if_neg h]

/-- Each row of the adjacency matrix of a `d`-regular graph sums to `d`. -/
theorem adjMatrix_mul_ones_of_regular (hd : G.IsRegularOfDegree d) :
    G.adjMatrix R * Matrix.of (fun _ _ => 1) = Matrix.of fun _ _ => (d : R) := by
  ext x y
  rw [adjMatrix_mul_apply]
  simp only [Matrix.of_apply, Finset.sum_const, card_neighborFinset_eq_degree, hd x, nsmul_eq_mul,
    mul_one]

/-- Two distinct vertices of a friendship graph have a *unique* common neighbour. -/
theorem eq_of_mem_commonNeighbors (hG : Friendship G) {v w a b : V} (hvw : v ≠ w)
    (ha : a ∈ G.commonNeighbors v w) (hb : b ∈ G.commonNeighbors v w) : a = b := by
  obtain ⟨c, hc⟩ := Fintype.card_eq_one_iff.1 (hG hvw)
  have := hc ⟨a, ha⟩
  have := hc ⟨b, hb⟩
  aesop

end Basic

section NoPolitician

variable [Nonempty V]

/-- A friendship graph with no politician is regular. -/
theorem isRegular_of_not_existsPolitician (hG : Friendship G) (hG' : ¬ExistsPolitician G) :
    ∃ d : ℕ, G.IsRegularOfDegree d := by
  have v := Classical.arbitrary V
  refine ⟨G.degree v, fun x => ?_⟩
  by_cases hvx : G.Adj v x
  swap
  · exact (degree_eq_of_not_adj hG hvx).symm
  rw [ExistsPolitician] at hG'
  push_neg at hG'
  obtain ⟨w, hvw', hvw⟩ := hG' v
  obtain ⟨y, hxy', hxy⟩ := hG' x
  by_cases hxw : G.Adj x w
  swap
  · rw [degree_eq_of_not_adj hG hvw]
    exact degree_eq_of_not_adj hG hxw
  by_cases hvy : G.Adj v y
  swap
  · rw [degree_eq_of_not_adj hG hvy]
    exact degree_eq_of_not_adj hG hxy
  -- the remaining case is impossible: `x` and `y` would be two common neighbours of `v` and `w`
  have hwy : ¬G.Adj w y := by
    intro hcontra
    exact hxy' (eq_of_mem_commonNeighbors hG hvw'
      ((mem_commonNeighbors G).2 ⟨hvx, G.symm hxw⟩)
      ((mem_commonNeighbors G).2 ⟨hvy, hcontra⟩))
  rw [degree_eq_of_not_adj hG hvw, degree_eq_of_not_adj hG hwy]
  exact degree_eq_of_not_adj hG hxy

/-- Counting length-two walks starting at a fixed vertex in a `d`-regular friendship graph
shows the graph has `d * d - d + 1` vertices. -/
theorem card_of_regular (hG : Friendship G) (hd : G.IsRegularOfDegree d) :
    d + (Fintype.card V - 1) = d * d := by
  have hsq := adjMatrix_sq_of_regular (R := ℕ) hG hd
  have v := Classical.arbitrary V
  have hA : ∑ w, (G.adjMatrix ℕ ^ 2 : Matrix V V ℕ) v w = d + (Fintype.card V - 1) := by
    rw [hsq, ← Finset.add_sum_erase _ _ (mem_univ v)]
    simp only [Matrix.of_apply]
    congr 1
    rw [Finset.sum_congr rfl fun w hw => if_neg (Finset.ne_of_mem_erase hw).symm,
      Finset.sum_const, Finset.card_erase_of_mem (mem_univ v), Finset.card_univ, smul_eq_mul,
      mul_one]
  have hB : ∑ w, (G.adjMatrix ℕ ^ 2 : Matrix V V ℕ) v w = d * d := by
    have hrow : ∀ w, (G.adjMatrix ℕ ^ 2 : Matrix V V ℕ) v w
        = ∑ u ∈ G.neighborFinset v, (G.adjMatrix ℕ) u w := by
      intro w
      rw [show (2 : ℕ) = 1 + 1 from rfl, pow_succ', pow_one, adjMatrix_mul_apply]
    rw [Finset.sum_congr rfl fun w _ => hrow w, Finset.sum_comm]
    have hdeg : ∀ u ∈ G.neighborFinset v, ∑ w, (G.adjMatrix ℕ) u w = d := by
      intro u _
      simp [adjMatrix_apply, Finset.sum_boole, ← neighborFinset_eq_filter, hd u]
    rw [Finset.sum_congr rfl hdeg, Finset.sum_const, card_neighborFinset_eq_degree, hd v,
      smul_eq_mul]
  rw [← hA, hB]

end NoPolitician

section SmallDegree

variable [Nonempty V]

theorem existsPolitician_of_degree_le_two (hG : Friendship G) (hd : G.IsRegularOfDegree d)
    (h : d ≤ 2) : ExistsPolitician G := by
  have hcard := card_of_regular hG hd
  have hpos : 0 < Fintype.card V := Fintype.card_pos
  interval_cases d
  · have hle : Fintype.card V ≤ 1 := by omega
    exact ⟨Classical.arbitrary V, fun w hvw =>
      absurd (Fintype.card_le_one_iff.1 hle _ w) hvw⟩
  · have hle : Fintype.card V ≤ 1 := by omega
    exact ⟨Classical.arbitrary V, fun w hvw =>
      absurd (Fintype.card_le_one_iff.1 hle _ w) hvw⟩
  · -- a `2`-regular friendship graph is a triangle
    have hn : Fintype.card V = 3 := by omega
    set v := Classical.arbitrary V
    have hsub : G.neighborFinset v ⊆ univ.erase v := by
      intro x hx
      rw [mem_neighborFinset] at hx
      exact Finset.mem_erase.2 ⟨(G.ne_of_adj hx).symm, mem_univ _⟩
    have hcard2 : (univ.erase v).card = 2 := by
      rw [Finset.card_erase_of_mem (mem_univ v), Finset.card_univ, hn]
    have hnb : G.neighborFinset v = univ.erase v :=
      Finset.eq_of_subset_of_card_le hsub
        (by rw [hcard2, card_neighborFinset_eq_degree, hd v])
    refine ⟨v, fun w hvw => ?_⟩
    rw [← mem_neighborFinset, hnb, Finset.mem_erase]
    exact ⟨hvw.symm, mem_univ _⟩

end SmallDegree

section LargeDegree

variable [Nonempty V]

omit [Nonempty V] in
/-- Modulo a prime factor `p` of `d - 1`, all powers `≥ 2` of the adjacency matrix of a
`d`-regular friendship graph are the all-ones matrix. -/
theorem adjMatrix_pow_mod_p_of_regular (hG : Friendship G) {p : ℕ} (dmod : (d : ZMod p) = 1)
    (hd : G.IsRegularOfDegree d) {k : ℕ} (hk : 2 ≤ k) :
    G.adjMatrix (ZMod p) ^ k = Matrix.of fun _ _ => 1 := by
  have hones : G.adjMatrix (ZMod p) * Matrix.of (fun _ _ => 1) = Matrix.of fun _ _ => 1 := by
    rw [adjMatrix_mul_ones_of_regular hd, dmod]
  have hbase : G.adjMatrix (ZMod p) ^ 2 = Matrix.of fun _ _ => (1 : ZMod p) := by
    rw [adjMatrix_sq_of_regular hG hd, dmod]
    simp
  induction k, hk using Nat.le_induction with
  | base => exact hbase
  | succ n hn ih => rw [pow_succ', ih, hones]

/-- The number of vertices of a `d`-regular friendship graph is `1` modulo any `p` with
`d ≡ 1 [MOD p]`. -/
theorem card_mod_p_of_regular (hG : Friendship G) {p : ℕ} (dmod : (d : ZMod p) = 1)
    (hd : G.IsRegularOfDegree d) : (Fintype.card V : ZMod p) = 1 := by
  have hcard := card_of_regular hG hd
  have hpos : 0 < Fintype.card V := Fintype.card_pos
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card V = m + 1 := ⟨Fintype.card V - 1, by omega⟩
  have hdm : d + m = d * d := by omega
  have := congrArg (fun n : ℕ => (n : ZMod p)) hdm
  simp only [Nat.cast_add, Nat.cast_mul, dmod, one_mul] at this
  have hm0 : (m : ZMod p) = 0 := by linear_combination this
  rw [hm, Nat.cast_add, hm0, Nat.cast_one, zero_add]

/-- There is no `d`-regular friendship graph with `3 ≤ d`. -/
theorem false_of_three_le_degree (hG : Friendship G) (hd : G.IsRegularOfDegree d) (h : 3 ≤ d) :
    False := by
  set p : ℕ := (d - 1).minFac
  haveI : Fact p.Prime := ⟨Nat.minFac_prime (by omega)⟩
  have hp2 : 2 ≤ p := (Fact.out (p := p.Prime)).two_le
  have hdvd : ((d - 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 (d - 1).minFac_dvd
  have dmod : (d : ZMod p) = 1 := by
    have : ((d - 1 : ℕ) : ZMod p) = (d : ZMod p) - 1 := by
      have : ((d - 1 : ℕ) : ℤ) = (d : ℤ) - 1 := by omega
      exact_mod_cast congrArg (fun z : ℤ => (z : ZMod p)) this
    rw [this] at hdvd
    linear_combination hdvd
  have hVmod := card_mod_p_of_regular hG dmod hd
  have htrace := ZMod.trace_pow_card (G.adjMatrix (ZMod p))
  rw [trace_adjMatrix, zero_pow (by omega : p ≠ 0),
    adjMatrix_pow_mod_p_of_regular hG dmod hd hp2, Matrix.trace] at htrace
  simp only [Matrix.diag_apply, Matrix.of_apply, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one] at htrace
  rw [hVmod] at htrace
  exact one_ne_zero htrace

end LargeDegree

/-- **The friendship theorem** (Erdős–Rényi–Sós): if in a finite nonempty graph every two
distinct vertices have exactly one common neighbour, then some vertex is adjacent to all
other vertices. -/
theorem friendship_theorem [Nonempty V] (hG : Friendship G) : ExistsPolitician G := by
  by_contra hG'
  obtain ⟨d, hd⟩ := isRegular_of_not_existsPolitician hG hG'
  rcases lt_or_ge d 3 with h | h
  · exact hG' (existsPolitician_of_degree_le_two hG hd (by omega))
  · exact false_of_three_le_degree hG hd h

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

