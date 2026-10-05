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

import Mathlib

/-!
# Friendship Theorem
Category: Frontier — Fields Medal Work
Target: Frontier.friendship_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open Finset Matrix SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A graph satisfies the *friendship condition* when any two distinct vertices have
exactly one common neighbour ("every two people have exactly one common friend"). -/
def Friendship (G : SimpleGraph V) : Prop :=
  ∀ ⦃v w : V⦄, v ≠ w → ∃! u : V, G.Adj v u ∧ G.Adj w u

variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Under the friendship condition, two distinct vertices have exactly one common neighbour. -/
lemma card_common_neighbors_eq_one (hG : Friendship G) {v w : V} (h : v ≠ w) :
    (G.neighborFinset v ∩ G.neighborFinset w).card = 1 := by
  obtain ⟨u, hu, huniq⟩ := hG h
  rw [Finset.card_eq_one]
  refine ⟨u, ?_⟩
  ext x
  simp only [Finset.mem_inter, mem_neighborFinset, Finset.mem_singleton]
  constructor
  · rintro ⟨h1, h2⟩
    exact huniq x ⟨h1, h2⟩
  · rintro rfl
    exact hu

/-- The square of the adjacency matrix counts common neighbours. -/
lemma adjMatrix_sq_apply (α : Type*) [Semiring α] (v w : V) :
    (G.adjMatrix α * G.adjMatrix α) v w = ((G.neighborFinset v ∩ G.neighborFinset w).card : α) := by
  rw [adjMatrix_mul_apply]
  simp only [adjMatrix_apply]
  rw [Finset.sum_boole]
  congr 2
  ext x
  simp [mem_neighborFinset, adj_comm]

/-- Under the friendship condition, a vertex has degree at most that of any distinct
non-adjacent vertex. -/
lemma degree_le_of_not_adj (hG : Friendship G) {v w : V} (hvw : v ≠ w) (h : ¬ G.Adj v w) :
    G.degree v ≤ G.degree w := by
  classical
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
  have key : ∀ x : V, x ≠ w → ∃ u, G.Adj x u ∧ G.Adj w u := fun x hx => (hG hx).exists
  set F : V → V := fun x => if hx : x = w then x else (key x hx).choose with hF
  have hFspec : ∀ x : V, x ≠ w → G.Adj x (F x) ∧ G.Adj w (F x) := by
    intro x hx
    simp only [hF, dif_neg hx]
    exact (key x hx).choose_spec
  apply Finset.card_le_card_of_injOn F
  · intro x hx
    simp only [Finset.mem_coe, mem_neighborFinset] at hx ⊢
    have hxw : x ≠ w := by rintro rfl; exact h hx
    exact (hFspec x hxw).2
  · intro x hx y hy hxy
    simp only [Finset.mem_coe, mem_neighborFinset] at hx hy
    have hxw : x ≠ w := by rintro rfl; exact h hx
    have hyw : y ≠ w := by rintro rfl; exact h hy
    by_contra hne
    have h1 : G.Adj x (F x) ∧ G.Adj y (F x) :=
      ⟨(hFspec x hxw).1, by rw [hxy]; exact (hFspec y hyw).1⟩
    have h2 : G.Adj x v ∧ G.Adj y v := ⟨hx.symm, hy.symm⟩
    have hvF := (hG hne).unique h1 h2
    rw [← hvF] at h
    exact h ((hFspec x hxw).2).symm

/-- Two distinct non-adjacent vertices of a friendship graph have the same degree. -/
lemma degree_eq_of_not_adj (hG : Friendship G) {v w : V} (hvw : v ≠ w) (h : ¬ G.Adj v w) :
    G.degree v = G.degree w :=
  le_antisymm (degree_le_of_not_adj hG hvw h)
    (degree_le_of_not_adj hG hvw.symm fun ha => h ha.symm)

/-- If a friendship graph has no vertex adjacent to all others, then it is regular. -/
lemma exists_regular_of_no_politician (hG : Friendship G)
    (hnp : ∀ u : V, ∃ w : V, w ≠ u ∧ ¬ G.Adj u w) (v₀ : V) :
    ∃ d : ℕ, ∀ v : V, G.degree v = d := by
  refine ⟨G.degree v₀, fun v => ?_⟩
  suffices key : ∀ a b : V, G.degree a = G.degree b from key v v₀
  intro a b
  rcases eq_or_ne a b with rfl | hab
  · rfl
  by_cases hadj : G.Adj a b
  swap
  · exact degree_eq_of_not_adj hG hab hadj
  obtain ⟨x, hxa, hax⟩ := hnp a
  obtain ⟨y, hyb, hby⟩ := hnp b
  have hxb : x ≠ b := by rintro rfl; exact hax hadj
  have hya : y ≠ a := by rintro rfl; exact hby hadj.symm
  by_cases hbx : G.Adj b x
  · by_cases hay : G.Adj a y
    · have hxy : x ≠ y := by rintro rfl; exact hax hay
      by_cases hxyadj : G.Adj x y
      · -- a four-cycle `a - b - x - y - a` would give `a` and `x` two common neighbours
        exfalso
        have h1 : G.Adj a b ∧ G.Adj x b := ⟨hadj, hbx.symm⟩
        have h2 : G.Adj a y ∧ G.Adj x y := ⟨hay, hxyadj⟩
        exact hyb ((hG (Ne.symm hxa)).unique h1 h2).symm
      · have e1 : G.degree a = G.degree x := degree_eq_of_not_adj hG (Ne.symm hxa) hax
        have e2 : G.degree x = G.degree y := degree_eq_of_not_adj hG hxy hxyadj
        have e3 : G.degree b = G.degree y := degree_eq_of_not_adj hG (Ne.symm hyb) hby
        rw [e1, e2, e3]
    · have e1 : G.degree a = G.degree y := degree_eq_of_not_adj hG (Ne.symm hya) hay
      have e3 : G.degree b = G.degree y := degree_eq_of_not_adj hG (Ne.symm hyb) hby
      rw [e1, e3]
  · have e1 : G.degree a = G.degree x := degree_eq_of_not_adj hG (Ne.symm hxa) hax
    have e2 : G.degree b = G.degree x := degree_eq_of_not_adj hG (Ne.symm hxb) hbx
    rw [e1, e2]

/-- Counting identity for a `d`-regular friendship graph on `n` vertices: `d² + 1 = d + n`. -/
lemma card_eq_of_regular (hG : Friendship G) {d : ℕ} (hd : ∀ v : V, G.degree v = d) (v : V) :
    d * d + 1 = d + Fintype.card V := by
  have hrow : ∀ u : V, ∑ w : V, (G.adjMatrix ℕ) u w = d := by
    intro u
    simp [adjMatrix_apply, Finset.sum_boole, ← neighborFinset_eq_filter, hd]
  have hsum1 : ∑ w : V, (G.adjMatrix ℕ * G.adjMatrix ℕ) v w = d * d := by
    simp only [adjMatrix_mul_apply]
    rw [Finset.sum_comm]
    simp only [hrow]
    rw [Finset.sum_const, card_neighborFinset_eq_degree, hd, smul_eq_mul]
  have hsum2 : ∑ w : V, (G.adjMatrix ℕ * G.adjMatrix ℕ) v w = d + (Fintype.card V - 1) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ v)]
    congr 1
    · rw [adjMatrix_sq_apply, Finset.inter_self, card_neighborFinset_eq_degree, hd, Nat.cast_id]
    · rw [Finset.sum_congr rfl (fun w hw => ?_), Finset.sum_const, Finset.card_erase_of_mem
        (Finset.mem_univ v), Finset.card_univ, smul_eq_mul, mul_one]
      rw [adjMatrix_sq_apply, card_common_neighbors_eq_one hG (Ne.symm (Finset.ne_of_mem_erase hw))]
      norm_num
  have hcard : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
  omega

/-- A regular friendship graph without a vertex adjacent to all others has degree at least
three. -/
lemma three_le_degree (hG : Friendship G) (hnp : ∀ u : V, ∃ w : V, w ≠ u ∧ ¬ G.Adj u w)
    {d : ℕ} (hd : ∀ v : V, G.degree v = d) (v : V) : 3 ≤ d := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨w, hwv, hvw⟩ := hnp v
  obtain ⟨u, ⟨hvu, hwu⟩, -⟩ := hG (Ne.symm hwv)
  interval_cases d
  · -- degree `0` is impossible: `u` is a neighbour of `v`
    have hmem : u ∈ G.neighborFinset v := by rw [mem_neighborFinset]; exact hvu
    have hpos := Finset.card_pos.mpr ⟨u, hmem⟩
    rw [card_neighborFinset_eq_degree, hd] at hpos
    omega
  · -- degree `1` is impossible: `u` is adjacent to both `v` and `w`
    have hsub : ({v, w} : Finset V) ⊆ G.neighborFinset u := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · rw [mem_neighborFinset]; exact hvu.symm
      · rw [mem_neighborFinset]; exact hwu.symm
    have hcard := Finset.card_le_card hsub
    rw [card_neighborFinset_eq_degree, hd,
      Finset.card_insert_of_notMem (by simpa using Ne.symm hwv), Finset.card_singleton] at hcard
    omega
  · -- degree `2` is impossible: then there are only three vertices
    have hcardV := card_eq_of_regular hG hd v
    have hsub : G.neighborFinset v ⊆ (Finset.univ.erase v).erase w := by
      intro x hx
      rw [mem_neighborFinset] at hx
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_, Finset.mem_univ x⟩⟩
      · rintro rfl; exact hvw hx
      · rintro rfl; exact G.irrefl hx
    have hc := Finset.card_le_card hsub
    rw [card_neighborFinset_eq_degree, hd, Finset.card_erase_of_mem
      (Finset.mem_erase.mpr ⟨hwv, Finset.mem_univ w⟩), Finset.card_erase_of_mem (Finset.mem_univ v),
      Finset.card_univ] at hc
    omega

/-- The main counting contradiction: a regular friendship graph of degree at least three cannot
exist.  Working modulo a prime `p` dividing `d - 1`, the adjacency matrix `A` satisfies
`A ^ k = J` (the all-ones matrix) for all `k ≥ 2`; comparing `trace (A ^ p) = (trace A) ^ p = 0`
with `trace J = n = 1` gives `1 = 0` in `ZMod p`. -/
lemma false_of_three_le_degree (hG : Friendship G) {d : ℕ} (hd : ∀ v : V, G.degree v = d)
    (hd3 : 3 ≤ d) (v : V) : False := by
  have hpp : Nat.Prime (d - 1).minFac := Nat.minFac_prime (by omega)
  set p := (d - 1).minFac with hpdef
  haveI : Fact (Nat.Prime p) := ⟨hpp⟩
  have hpdvd : p ∣ d - 1 := Nat.minFac_dvd _
  have hdp : (d : ZMod p) = 1 := by
    have h0 : ((d - 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hpdvd
    rw [Nat.cast_sub (show 1 ≤ d by omega), Nat.cast_one, sub_eq_zero] at h0
    exact h0
  have hcardV : (Fintype.card V : ZMod p) = 1 := by
    have h := card_eq_of_regular hG hd v
    have h2 : ((d * d + 1 : ℕ) : ZMod p) = ((d + Fintype.card V : ℕ) : ZMod p) := by
      exact_mod_cast congrArg (fun n : ℕ => (n : ZMod p)) h
    push_cast [hdp] at h2
    linear_combination -h2
  set A := G.adjMatrix (ZMod p) with hA
  set J : Matrix V V (ZMod p) := Matrix.of (fun _ _ => 1) with hJ
  have hA2 : A * A = J := by
    ext x y
    rw [hA, adjMatrix_sq_apply]
    rcases eq_or_ne x y with rfl | hxy
    · rw [Finset.inter_self, card_neighborFinset_eq_degree, hd, hJ]
      simpa using hdp
    · rw [card_common_neighbors_eq_one hG hxy, hJ]
      simp
  have hJA : J * A = J := by
    ext x y
    rw [hA, mul_adjMatrix_apply]
    simp only [hJ, Matrix.of_apply, Finset.sum_const, card_neighborFinset_eq_degree, hd,
      nsmul_eq_mul, mul_one, hdp]
  have hApow : ∀ k, 2 ≤ k → A ^ k = J := by
    intro k hk
    induction k with
    | zero => omega
    | succ n ih =>
      rcases Nat.lt_or_ge n 2 with h | h
      · interval_cases n
        · omega
        · rw [pow_succ, pow_one]; exact hA2
      · rw [pow_succ, ih h, hJA]
  have htr : Matrix.trace (A ^ p) = Matrix.trace A ^ p := ZMod.trace_pow_card A
  rw [hApow p hpp.two_le, hA, trace_adjMatrix, zero_pow hpp.ne_zero, Matrix.trace] at htr
  simp only [hJ, Matrix.diag_apply, Matrix.of_apply, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one, hcardV] at htr
  exact one_ne_zero htr

/-- **The Friendship Theorem** (Erdős–Ko–Rényi): in a finite nonempty graph in which every two
distinct vertices have exactly one common neighbour, there is a vertex adjacent to all the
others. -/
theorem friendship_theorem [Nonempty V] (hG : Friendship G) :
    ∃ u : V, ∀ w : V, w ≠ u → G.Adj u w := by
  by_contra hc
  push_neg at hc
  obtain ⟨v⟩ := ‹Nonempty V›
  have hnp : ∀ u : V, ∃ w : V, w ≠ u ∧ ¬ G.Adj u w := by
    intro u
    obtain ⟨w, hw, hadj⟩ := hc u
    exact ⟨w, hw, hadj⟩
  obtain ⟨d, hd⟩ := exists_regular_of_no_politician hG hnp v
  exact false_of_three_le_degree hG hd (three_le_degree hG hnp hd v) v

/-- The hypothesis of `friendship_theorem` is satisfiable: the triangle is a friendship graph,
so the theorem is not vacuous. -/
theorem friendship_triangle : Friendship (⊤ : SimpleGraph (Fin 3)) := by
  intro v w h
  fin_cases v <;> fin_cases w <;> simp_all <;>
    first
      | exact ⟨0, by decide, by decide⟩
      | exact ⟨1, by decide, by decide⟩
      | exact ⟨2, by decide, by decide⟩

end Frontier

