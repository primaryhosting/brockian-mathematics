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

/-
# Friendship Theorem
Category: Frontier — Fields Medal Work
Target: Frontier.friendship_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
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
  {d : ℕ}

/-- The friendship hypothesis: any two distinct vertices have exactly one common neighbour. -/
def UniqueCommonFriend {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ v w : V, v ≠ w → ∃! u : V, G.Adj v u ∧ G.Adj w u

/-- A politician: a vertex adjacent to every other vertex. -/
def IsPolitician {V : Type*} (G : SimpleGraph V) (v : V) : Prop :=
  ∀ w : V, v ≠ w → G.Adj v w

section Basic

theorem card_filter_eq_one_of_existsUnique {P : V → Prop} [DecidablePred P] (h : ∃! u, P u) :
    ({u | P u} : Finset V).card = 1 := by
  obtain ⟨u, hu, huniq⟩ := h
  rw [Finset.card_eq_one]
  exact ⟨u, by ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton]; exact ⟨fun hx => huniq x hx, fun hx => hx ▸ hu⟩⟩

/-- The `(v, w)` entry of the square of the adjacency matrix counts common neighbours. -/
theorem adjMatrix_sq_apply (R : Type*) [Semiring R] (v w : V) :
    (G.adjMatrix R ^ 2) v w = (({u | G.Adj v u ∧ G.Adj w u} : Finset V).card : R) := by
  simp [sq, Matrix.mul_apply, adjMatrix_apply, Finset.sum_ite, adj_comm, Finset.filter_filter,
    and_comm]

/-- In a friendship graph, the off-diagonal entries of `A ^ 2` are all `1`. -/
theorem adjMatrix_sq_of_ne (hG : UniqueCommonFriend G) (R : Type*) [Semiring R] {v w : V}
    (h : v ≠ w) : (G.adjMatrix R ^ 2) v w = 1 := by
  rw [adjMatrix_sq_apply, card_filter_eq_one_of_existsUnique (hG v w h), Nat.cast_one]

/-- Counting walks of length three between nonadjacent vertices. -/
theorem adjMatrix_pow_three_of_not_adj (hG : UniqueCommonFriend G) (R : Type*) [Semiring R]
    {v w : V} (h : ¬ G.Adj v w) : (G.adjMatrix R ^ 3) v w = (G.degree v : R) := by
  have h3 : (G.adjMatrix R) ^ 3 = G.adjMatrix R * (G.adjMatrix R) ^ 2 := by rw [← pow_succ']
  rw [h3, adjMatrix_mul_apply]
  have : ∀ u ∈ G.neighborFinset v, ((G.adjMatrix R) ^ 2) u w = 1 := by
    intro u hu
    refine adjMatrix_sq_of_ne hG R ?_
    rintro rfl
    exact h (G.mem_neighborFinset v u |>.mp hu)
  rw [Finset.sum_congr rfl this]
  rw [Finset.sum_const, nsmul_eq_mul, mul_one, card_neighborFinset_eq_degree]

/-- Nonadjacent vertices of a friendship graph have the same degree. -/
theorem degree_eq_of_not_adj (hG : UniqueCommonFriend G) {v w : V} (h : ¬ G.Adj v w) :
    G.degree v = G.degree w := by
  have hs : ((G.adjMatrix ℕ) ^ 3)ᵀ = (G.adjMatrix ℕ) ^ 3 := by
    rw [Matrix.transpose_pow, transpose_adjMatrix]
  have h1 : ((G.adjMatrix ℕ) ^ 3) v w = G.degree v := adjMatrix_pow_three_of_not_adj hG ℕ h
  have h2 : ((G.adjMatrix ℕ) ^ 3) w v = G.degree w :=
    adjMatrix_pow_three_of_not_adj hG ℕ fun hc => h hc.symm
  have h3 : ((G.adjMatrix ℕ) ^ 3) v w = ((G.adjMatrix ℕ) ^ 3) w v := by
    conv_lhs => rw [← hs]
    rfl
  omega

end Basic

section Regular

/-- A friendship graph with no politician is regular. -/
theorem exists_isRegularOfDegree_of_not_politician [Nonempty V] (hG : UniqueCommonFriend G)
    (hnp : ¬ ∃ v : V, IsPolitician G v) : ∃ d : ℕ, G.IsRegularOfDegree d := by
  have hnp' : ∀ v : V, ∃ w : V, v ≠ w ∧ ¬ G.Adj v w := by
    simpa [IsPolitician, not_forall] using hnp
  refine ⟨G.degree (Classical.arbitrary V), fun x => ?_⟩
  set v := Classical.arbitrary V with hv
  by_cases hvx : G.Adj v x
  swap
  · exact (degree_eq_of_not_adj hG hvx).symm
  obtain ⟨w, hvw', hvw⟩ := hnp' v
  obtain ⟨y, hxy', hxy⟩ := hnp' x
  by_cases hxw : G.Adj x w
  swap
  · rw [degree_eq_of_not_adj hG hvw]
    exact degree_eq_of_not_adj hG hxw
  rw [degree_eq_of_not_adj hG hxy]
  by_cases hvy : G.Adj v y
  swap
  · exact (degree_eq_of_not_adj hG hvy).symm
  rw [degree_eq_of_not_adj hG hvw]
  refine degree_eq_of_not_adj hG (fun hyw => hxy' ?_)
  obtain ⟨a, -, huniq⟩ := hG v w hvw'
  rw [huniq x ⟨hvx, hxw.symm⟩, huniq y ⟨hvy, hyw.symm⟩]

/-- For a `d`-regular friendship graph, `A ^ 2` is determined completely. -/
theorem adjMatrix_sq_of_regular (hG : UniqueCommonFriend G) (R : Type*) [Semiring R]
    (hd : G.IsRegularOfDegree d) :
    G.adjMatrix R ^ 2 = Matrix.of fun v w => if v = w then (d : R) else (1 : R) := by
  ext v w
  rcases eq_or_ne v w with rfl | h
  · rw [sq, adjMatrix_mul_self_apply_self, hd]
    simp
  · rw [adjMatrix_sq_of_ne hG R h, Matrix.of_apply, if_neg h]

/-- A `d`-regular friendship graph has `d ^ 2 - d + 1` vertices. -/
theorem card_of_regular [Nonempty V] (hG : UniqueCommonFriend G) (hd : G.IsRegularOfDegree d) :
    d + (Fintype.card V - 1) = d * d := by
  have v := Classical.arbitrary V
  have key : ∑ w : V, ((G.adjMatrix ℕ) ^ 2) v w = d * d := by
    have h1 : ∀ u : V, ∑ w : V, (G.adjMatrix ℕ) u w = d := by
      intro u
      have hset : ({x | G.Adj u x} : Finset V) = G.neighborFinset u := by
        ext x; simp
      simp only [adjMatrix_apply, Finset.sum_boole, Nat.cast_id, hset,
        card_neighborFinset_eq_degree, hd u]
    calc ∑ w : V, ((G.adjMatrix ℕ) ^ 2) v w
        = ∑ w : V, ∑ u : V, (G.adjMatrix ℕ) v u * (G.adjMatrix ℕ) u w := by
          simp [sq, Matrix.mul_apply]
      _ = ∑ u : V, ∑ w : V, (G.adjMatrix ℕ) v u * (G.adjMatrix ℕ) u w := Finset.sum_comm
      _ = ∑ u : V, (G.adjMatrix ℕ) v u * ∑ w : V, (G.adjMatrix ℕ) u w := by
          simp_rw [Finset.mul_sum]
      _ = d * d := by
          simp_rw [h1]
          rw [← Finset.sum_mul, h1 v]
  have key2 : ∑ w : V, ((G.adjMatrix ℕ) ^ 2) v w = d + (Fintype.card V - 1) := by
    rw [adjMatrix_sq_of_regular hG ℕ hd, ← Finset.sum_erase_add _ _ (Finset.mem_univ v)]
    simp only [Matrix.of_apply, Nat.cast_id, if_pos rfl]
    have : ∀ w ∈ Finset.univ.erase v, (if v = w then (d : ℕ) else 1) = 1 := fun w hw =>
      if_neg (Ne.symm (Finset.ne_of_mem_erase hw))
    rw [Finset.sum_congr rfl this, Finset.sum_const, smul_eq_mul, mul_one,
      Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ, Nat.add_comm]
    simp
  omega

end Regular

section SmallDegree

theorem exists_politician_of_degree_le_one (hG : UniqueCommonFriend G) [Nonempty V]
    (hd : G.IsRegularOfDegree d) (hd1 : d ≤ 1) : ∃ v : V, IsPolitician G v := by
  have h := card_of_regular hG hd
  have hsq : d * d = d := by interval_cases d <;> norm_num
  rw [hsq] at h
  have hcard : Fintype.card V ≤ 1 := by
    have : 0 < Fintype.card V := Fintype.card_pos
    omega
  exact ⟨Classical.arbitrary V, fun w hw => absurd (Fintype.card_le_one_iff.mp hcard _ w) hw⟩

theorem exists_politician_of_degree_eq_two (hG : UniqueCommonFriend G) [Nonempty V]
    (hd : G.IsRegularOfDegree 2) : ∃ v : V, IsPolitician G v := by
  have h := card_of_regular hG hd
  have hn : Fintype.card V = 3 := by
    have : 0 < Fintype.card V := Fintype.card_pos
    omega
  refine ⟨Classical.arbitrary V, fun w hw => ?_⟩
  set v := Classical.arbitrary V with hv
  have hsub : G.neighborFinset v ⊆ Finset.univ.erase v := by
    intro x hx
    rw [mem_neighborFinset] at hx
    exact Finset.mem_erase.mpr ⟨(G.ne_of_adj hx).symm, Finset.mem_univ _⟩
  have hcards : (Finset.univ.erase v).card ≤ (G.neighborFinset v).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), card_neighborFinset_eq_degree, hd v,
      Finset.card_univ, hn]
  have heq : G.neighborFinset v = Finset.univ.erase v := Finset.eq_of_subset_of_card_le hsub hcards
  rw [← mem_neighborFinset, heq]
  exact Finset.mem_erase.mpr ⟨hw.symm, Finset.mem_univ _⟩

theorem exists_politician_of_degree_le_two (hG : UniqueCommonFriend G) [Nonempty V]
    (hd : G.IsRegularOfDegree d) (h : d ≤ 2) : ∃ v : V, IsPolitician G v := by
  interval_cases d
  · exact exists_politician_of_degree_le_one hG hd (by norm_num)
  · exact exists_politician_of_degree_le_one hG hd (by norm_num)
  · exact exists_politician_of_degree_eq_two hG hd

end SmallDegree

section LargeDegree

/-- For a `d`-regular friendship graph, `A * J = d • J`, where `J` is the all-ones matrix. -/
theorem adjMatrix_mul_allOnes (R : Type*) [Semiring R] (hd : G.IsRegularOfDegree d) :
    G.adjMatrix R * Matrix.of (fun _ _ => (1 : R)) = Matrix.of (fun _ _ => (d : R)) := by
  ext v w
  rw [adjMatrix_mul_apply]
  simp only [Matrix.of_apply]
  rw [Finset.sum_const, nsmul_eq_mul, mul_one, card_neighborFinset_eq_degree, hd v]

/-- Modulo a prime factor `p` of `d - 1`, all powers `A ^ k` with `2 ≤ k` of the adjacency matrix
of a `d`-regular friendship graph are the all-ones matrix. -/
theorem adjMatrix_pow_mod_p (hG : UniqueCommonFriend G) {p : ℕ} (dmod : (d : ZMod p) = 1)
    (hd : G.IsRegularOfDegree d) : ∀ k : ℕ, 2 ≤ k →
      G.adjMatrix (ZMod p) ^ k = Matrix.of (fun _ _ => (1 : ZMod p)) := by
  intro k hk
  induction k with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge n 2 with hn | hn
    · have hn2 : n = 1 := by omega
      subst hn2
      rw [adjMatrix_sq_of_regular hG (ZMod p) hd]
      ext v w
      rcases eq_or_ne v w with rfl | hvw
      · simp [dmod]
      · simp [hvw]
    · rw [pow_succ', ih hn, adjMatrix_mul_allOnes (ZMod p) hd, dmod]

theorem false_of_three_le_degree [Nonempty V] (hG : UniqueCommonFriend G)
    (hd : G.IsRegularOfDegree d) (h : 3 ≤ d) : False := by
  set p := (d - 1).minFac with hp
  haveI : Fact p.Prime := ⟨Nat.minFac_prime (by omega)⟩
  have hp2 : 2 ≤ p := (Fact.out (p := p.Prime)).two_le
  have hdvd : ((d - 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr (Nat.minFac_dvd _)
  have dmod : (d : ZMod p) = 1 := by
    have hd1 : ((d - 1 : ℕ) + 1 : ℕ) = d := by omega
    have hsplit : ((d - 1 : ℕ) : ZMod p) + 1 = (d : ZMod p) := by
      simpa using congrArg (fun n : ℕ => (n : ZMod p)) hd1
    rw [← hsplit, hdvd, zero_add]
  -- the number of vertices is `1` modulo `p`
  have hcard : (Fintype.card V : ZMod p) = 1 := by
    have hpos : 0 < Fintype.card V := Fintype.card_pos
    have hreg := card_of_regular hG hd
    obtain ⟨D, hD⟩ : ∃ D, d * d = D := ⟨_, rfl⟩
    rw [hD] at hreg
    have hlin : Fintype.card V + d = D + 1 := by omega
    have := congrArg (fun n : ℕ => (n : ZMod p)) hlin
    simp only [Nat.cast_add, Nat.cast_one, ← hD, Nat.cast_mul, dmod, mul_one] at this
    linear_combination this
  -- the trace of `A ^ p` is `1`, but it is also `(trace A) ^ p = 0`
  have htr := ZMod.trace_pow_card (G.adjMatrix (ZMod p))
  rw [trace_adjMatrix, zero_pow (by omega : p ≠ 0), adjMatrix_pow_mod_p hG dmod hd p hp2] at htr
  rw [Matrix.trace] at htr
  simp only [Matrix.diag_apply, Matrix.of_apply, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one] at htr
  rw [hcard] at htr
  exact one_ne_zero htr

end LargeDegree

/-- **Friendship theorem** (Erdős–Rényi–Sós): in a finite nonempty graph in which every two
distinct vertices have exactly one common neighbour, some vertex is adjacent to all others. -/
theorem friendship_theorem {V : Type*} [Fintype V] [Nonempty V] {G : SimpleGraph V}
    (hG : ∀ v w : V, v ≠ w → ∃! u : V, G.Adj v u ∧ G.Adj w u) :
    ∃ v : V, ∀ w : V, v ≠ w → G.Adj v w := by
  classical
  by_contra hnp
  obtain ⟨d, hd⟩ := exists_isRegularOfDegree_of_not_politician hG hnp
  rcases lt_or_ge d 3 with hlt | hge
  · exact hnp (exists_politician_of_degree_le_two hG hd (by omega))
  · exact false_of_three_le_degree hG hd hge

end Frontier

