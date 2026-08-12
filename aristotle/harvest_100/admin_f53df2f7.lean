import RequestProject.Friendship
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
# The friendship theorem (Erdős–Rényi–Sós)

If `G` is a finite graph in which every two distinct vertices have exactly one common
neighbour, then `G` has a vertex adjacent to all other vertices (a "politician").

The proof follows the classical argument:
* nonadjacent vertices have equal degrees (a length-3 walk count);
* hence a friendship graph with no politician is `d`-regular;
* a `d`-regular friendship graph has `d ^ 2 - d + 1` vertices;
* the cases `d ≤ 2` are handled directly;
* for `d ≥ 3` we pick a prime `p ∣ d - 1` and compare two computations of the trace of
  `A ^ p`, where `A` is the adjacency matrix over `ZMod p`.
-/

namespace Frontier

open Finset SimpleGraph Matrix

section Defs

variable {V : Type*} (G : SimpleGraph V)

/-- The friendship hypothesis: any two distinct vertices have exactly one common neighbour. -/
def IsFriendship : Prop := ∀ v w : V, v ≠ w → ∃! u : V, G.Adj v u ∧ G.Adj w u

/-- A *politician* is a vertex adjacent to every other vertex. -/
def HasPolitician : Prop := ∃ v : V, ∀ w : V, v ≠ w → G.Adj v w

end Defs

variable {V : Type*} [Fintype V] {G : SimpleGraph V} {d : ℕ}

section Matrices

variable [DecidableEq V] [DecidableRel G.Adj]

omit [DecidableEq V] in
/-- Summing a row of the adjacency matrix gives the degree. -/
theorem sum_adjMatrix_row (u : V) : ∑ w, (G.adjMatrix ℕ) u w = G.degree u := by
  simp [adjMatrix_apply, SimpleGraph.degree, neighborFinset_eq_filter, Finset.sum_boole]

variable {R : Type*} [Semiring R]

/-- Off-diagonal entries of the square of the adjacency matrix of a friendship graph are `1`. -/
theorem adjMatrix_sq_apply_of_ne (hG : IsFriendship G) {v w : V} (hvw : v ≠ w) :
    (G.adjMatrix R ^ 2 : Matrix V V R) v w = 1 := by
  obtain ⟨u, ⟨h1, h2⟩, huniq⟩ := hG v w hvw
  rw [sq, Matrix.mul_apply, Finset.sum_eq_single u]
  · simp [adjMatrix_apply, h1, h2.symm]
  · intro b _ hb
    rcases Classical.em (G.Adj v b) with hvb | hvb
    · have hbw : ¬ G.Adj b w := fun hbw => hb (huniq b ⟨hvb, hbw.symm⟩)
      simp [adjMatrix_apply, hbw]
    · simp [adjMatrix_apply, hvb]
  · intro h; exact absurd (Finset.mem_univ u) h

/-- For nonadjacent `v w`, the `(v, w)` entry of the cube of the adjacency matrix is the
degree of `v`: length-3 walks from `v` to `w` correspond to neighbours of `v`. -/
theorem adjMatrix_cube_apply_of_not_adj (hG : IsFriendship G) {v w : V} (h : ¬ G.Adj v w) :
    (G.adjMatrix R ^ 3 : Matrix V V R) v w = (G.degree v : R) := by
  have h3 : (G.adjMatrix R ^ 3 : Matrix V V R) = G.adjMatrix R * G.adjMatrix R ^ 2 := by
    rw [pow_succ']
  rw [h3, adjMatrix_mul_apply,
    Finset.sum_congr rfl (g := fun _ => (1 : R)) ?_]
  · rw [Finset.sum_const, ← card_neighborFinset_eq_degree, nsmul_eq_mul, mul_one]
  · intro x hx
    rw [mem_neighborFinset] at hx
    exact adjMatrix_sq_apply_of_ne hG (by rintro rfl; exact h hx)

end Matrices

/-- Nonadjacent vertices of a friendship graph have the same degree. -/
theorem degree_eq_of_not_adj [DecidableEq V] [DecidableRel G.Adj] (hG : IsFriendship G)
    {v w : V} (h : ¬ G.Adj v w) : G.degree v = G.degree w := by
  have hsymm : (G.adjMatrix ℕ ^ 3 : Matrix V V ℕ) v w = (G.adjMatrix ℕ ^ 3 : Matrix V V ℕ) w v := by
    have ht : ((G.adjMatrix ℕ ^ 3 : Matrix V V ℕ))ᵀ = (G.adjMatrix ℕ ^ 3 : Matrix V V ℕ) := by
      rw [Matrix.transpose_pow, transpose_adjMatrix]
    calc (G.adjMatrix ℕ ^ 3 : Matrix V V ℕ) v w
        = ((G.adjMatrix ℕ ^ 3 : Matrix V V ℕ))ᵀ w v := rfl
      _ = _ := by rw [ht]
  rw [← Nat.cast_id (G.degree v), ← Nat.cast_id (G.degree w),
    ← adjMatrix_cube_apply_of_not_adj (R := ℕ) hG h,
    ← adjMatrix_cube_apply_of_not_adj (R := ℕ) hG (fun hh => h hh.symm), hsymm]

/-- A friendship graph without a politician is regular. -/
theorem exists_isRegular_of_not_hasPolitician [DecidableEq V] [DecidableRel G.Adj] [Nonempty V]
    (hG : IsFriendship G) (hp : ¬ HasPolitician G) : ∃ d : ℕ, G.IsRegularOfDegree d := by
  classical
  have v₀ := Classical.arbitrary V
  refine ⟨G.degree v₀, fun x => ?_⟩
  by_cases hvx : G.Adj v₀ x
  swap
  · exact (degree_eq_of_not_adj hG hvx).symm
  -- both `v₀` and `x` have non-neighbours
  simp only [HasPolitician, not_exists, not_forall] at hp
  obtain ⟨w, hvw', hvw⟩ : ∃ w, v₀ ≠ w ∧ ¬ G.Adj v₀ w := by
    obtain ⟨w, hw⟩ := hp v₀
    exact ⟨w, hw.1, hw.2⟩
  obtain ⟨y, hxy', hxy⟩ : ∃ y, x ≠ y ∧ ¬ G.Adj x y := by
    obtain ⟨y, hy⟩ := hp x
    exact ⟨y, hy.1, hy.2⟩
  by_cases hxw : G.Adj x w
  swap
  · rw [degree_eq_of_not_adj hG hvw]
    exact degree_eq_of_not_adj hG hxw
  rw [degree_eq_of_not_adj hG hxy]
  by_cases hvy : G.Adj v₀ y
  swap
  · exact (degree_eq_of_not_adj hG hvy).symm
  rw [degree_eq_of_not_adj hG hvw]
  refine (degree_eq_of_not_adj hG (v := w) (w := y) ?_).symm
  intro hwy
  obtain ⟨u, _, huniq⟩ := hG v₀ w hvw'
  exact hxy' ((huniq x ⟨hvx, hxw.symm⟩).trans (huniq y ⟨hvy, hwy⟩).symm)

section Regular

variable [DecidableEq V] [DecidableRel G.Adj]

/-- The square of the adjacency matrix of a `d`-regular friendship graph. -/
theorem adjMatrix_sq_of_regular {R : Type*} [Semiring R] (hG : IsFriendship G)
    (hd : G.IsRegularOfDegree d) :
    (G.adjMatrix R ^ 2 : Matrix V V R) = Matrix.of fun v w => if v = w then (d : R) else 1 := by
  ext v w
  by_cases h : v = w
  · subst h
    rw [sq, adjMatrix_mul_self_apply_self, hd v]
    simp
  · rw [adjMatrix_sq_apply_of_ne hG h, Matrix.of_apply, if_neg h]

/-- A `d`-regular friendship graph has `d ^ 2 - d + 1` vertices. -/
theorem card_of_regular [Nonempty V] (hG : IsFriendship G) (hd : G.IsRegularOfDegree d) :
    d + (Fintype.card V - 1) = d * d := by
  have v := Classical.arbitrary V
  have hsq := adjMatrix_sq_of_regular (R := ℕ) hG hd
  have h1 : ∑ w, (G.adjMatrix ℕ ^ 2 : Matrix V V ℕ) v w = d + (Fintype.card V - 1) := by
    rw [hsq, ← Finset.add_sum_erase _ _ (mem_univ v)]
    simp only [Matrix.of_apply]
    congr 1
    rw [Finset.sum_congr rfl (g := fun _ => 1)
      (by intro x hx; rw [Finset.mem_erase] at hx; rw [if_neg (Ne.symm hx.1)])]
    simp [Finset.card_erase_of_mem, Finset.card_univ]
  have h2 : ∑ w, (G.adjMatrix ℕ ^ 2 : Matrix V V ℕ) v w = d * d := by
    rw [sq]
    simp only [adjMatrix_mul_apply]
    rw [Finset.sum_comm,
      Finset.sum_congr rfl (g := fun _ => d) (by intro x _; rw [sum_adjMatrix_row, hd x]),
      Finset.sum_const, card_neighborFinset_eq_degree, hd v, smul_eq_mul]
  omega

omit [DecidableEq V] in
/-- Multiplying the adjacency matrix of a `d`-regular graph with `d ≡ 1 [MOD p]` by the
all-ones matrix gives the all-ones matrix. -/
theorem adjMatrix_mul_ones {p : ℕ} (dmod : (d : ZMod p) = 1) (hd : G.IsRegularOfDegree d) :
    (G.adjMatrix (ZMod p)) * (Matrix.of fun _ _ => 1) = Matrix.of fun _ _ => (1 : ZMod p) := by
  ext v w
  rw [adjMatrix_mul_apply]
  simp only [Matrix.of_apply, Finset.sum_const, card_neighborFinset_eq_degree, hd v,
    nsmul_eq_mul, mul_one, dmod]

/-- Powers `≥ 2` of the adjacency matrix, modulo a prime factor `p` of `d - 1`, are all-ones. -/
theorem adjMatrix_pow_mod_p_of_regular {p : ℕ} (hG : IsFriendship G)
    (dmod : (d : ZMod p) = 1) (hd : G.IsRegularOfDegree d) {k : ℕ} (hk : 2 ≤ k) :
    (G.adjMatrix (ZMod p) ^ k) = Matrix.of fun _ _ => 1 := by
  induction k, hk using Nat.le_induction with
  | base =>
    rw [adjMatrix_sq_of_regular hG hd]
    ext v w
    by_cases h : v = w <;> simp [h, dmod]
  | succ k _ ih =>
    rw [pow_succ', ih, adjMatrix_mul_ones dmod hd]

/-- A `d`-regular friendship graph with `3 ≤ d` cannot exist. -/
theorem false_of_three_le_degree [Nonempty V] (hG : IsFriendship G)
    (hd : G.IsRegularOfDegree d) (h : 3 ≤ d) : False := by
  set p : ℕ := (d - 1).minFac with hp
  haveI : Fact p.Prime := ⟨Nat.minFac_prime (by omega)⟩
  have hp2 : 2 ≤ p := (Fact.out (p := p.Prime)).two_le
  have hdvd : ((d - 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr (d - 1).minFac_dvd
  have dmod : (d : ZMod p) = 1 := by
    have hcast : ((d - 1 : ℕ) : ZMod p) = (d : ZMod p) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one]
    rw [hcast] at hdvd
    linear_combination hdvd
  -- the number of vertices is `1` mod `p`
  have hcard : ((Fintype.card V : ℕ) : ZMod p) = 1 := by
    have hpos : 0 < Fintype.card V := Fintype.card_pos
    have hc := congrArg (fun n : ℕ => (n : ZMod p)) (card_of_regular hG hd)
    simp only [Nat.cast_add, Nat.cast_mul, dmod, one_mul] at hc
    have h0 : ((Fintype.card V - 1 : ℕ) : ZMod p) = 0 := by linear_combination hc
    have hsplit : (Fintype.card V : ℕ) = (Fintype.card V - 1) + 1 := by omega
    rw [hsplit, Nat.cast_add, h0, Nat.cast_one, zero_add]
  -- two computations of the trace of `A ^ p`
  have htr := ZMod.trace_pow_card (G.adjMatrix (ZMod p))
  rw [trace_adjMatrix, zero_pow (Fact.out (p := p.Prime)).ne_zero,
    adjMatrix_pow_mod_p_of_regular hG dmod hd hp2] at htr
  rw [Matrix.trace] at htr
  simp only [Matrix.diag_apply, Matrix.of_apply, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one] at htr
  rw [hcard] at htr
  exact one_ne_zero htr

/-- A `d`-regular friendship graph with `d ≤ 2` has a politician. -/
theorem hasPolitician_of_degree_le_two [Nonempty V] (hG : IsFriendship G)
    (hd : G.IsRegularOfDegree d) (h : d ≤ 2) : HasPolitician G := by
  have hc := card_of_regular hG hd
  have hpos : 0 < Fintype.card V := Fintype.card_pos
  interval_cases d
  · -- `d = 0`: at most one vertex
    refine ⟨Classical.arbitrary V, fun w hw => absurd ?_ hw⟩
    have : Fintype.card V ≤ 1 := by omega
    exact Fintype.card_le_one_iff.mp this _ _
  · -- `d = 1`: at most one vertex
    refine ⟨Classical.arbitrary V, fun w hw => absurd ?_ hw⟩
    have : Fintype.card V ≤ 1 := by omega
    exact Fintype.card_le_one_iff.mp this _ _
  · -- `d = 2`: three vertices, and each vertex is adjacent to the two others
    have hV : Fintype.card V = 3 := by omega
    refine ⟨Classical.arbitrary V, fun w hw => ?_⟩
    set v := Classical.arbitrary V
    have hsub : G.neighborFinset v ⊆ Finset.univ.erase v := by
      intro x hx
      rw [mem_neighborFinset] at hx
      exact Finset.mem_erase.mpr ⟨(G.ne_of_adj hx).symm, Finset.mem_univ _⟩
    have hcards : (Finset.univ.erase v).card ≤ (G.neighborFinset v).card := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), card_neighborFinset_eq_degree, hd v,
        Finset.card_univ, hV]
    have heq : G.neighborFinset v = Finset.univ.erase v :=
      Finset.eq_of_subset_of_card_le hsub hcards
    have : w ∈ G.neighborFinset v := by
      rw [heq]
      exact Finset.mem_erase.mpr ⟨hw.symm, Finset.mem_univ _⟩
    rwa [mem_neighborFinset] at this

end Regular

/-- **The friendship theorem** (Erdős–Rényi–Sós): in a finite nonempty graph in which every two
distinct vertices have exactly one common neighbour, some vertex is adjacent to all others. -/
theorem friendship_theorem {V : Type*} [Fintype V] [Nonempty V] {G : SimpleGraph V}
    (hG : ∀ v w : V, v ≠ w → ∃! u : V, G.Adj v u ∧ G.Adj w u) :
    ∃ v : V, ∀ w : V, v ≠ w → G.Adj v w := by
  classical
  by_contra hp
  obtain ⟨d, hd⟩ := exists_isRegular_of_not_hasPolitician (G := G) hG hp
  rcases lt_or_ge d 3 with hlt | hge
  · exact hp (hasPolitician_of_degree_le_two (d := d) hG hd (by omega))
  · exact false_of_three_le_degree hG hd hge

/-- The friendship theorem, phrased with `Fintype.card (G.commonNeighbors v w) = 1`. -/
theorem friendship_theorem' {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hG : ∀ v w : V, v ≠ w → Fintype.card (G.commonNeighbors v w) = 1) :
    ∃ v : V, ∀ w : V, v ≠ w → G.Adj v w := by
  refine friendship_theorem (fun v w hvw => ?_)
  obtain ⟨⟨u, hu⟩, huniq⟩ := Fintype.card_eq_one_iff.mp (hG v w hvw)
  rw [mem_commonNeighbors] at hu
  exact ⟨u, hu, fun y hy => congrArg Subtype.val (huniq ⟨y, (mem_commonNeighbors G).mpr hy⟩)⟩

/-- The hypothesis of the friendship theorem is satisfiable: the triangle is a friendship
graph (so the theorem is not vacuous). -/
example : ∀ v w : Fin 3, v ≠ w →
    ∃! u : Fin 3, (completeGraph (Fin 3)).Adj v u ∧ (completeGraph (Fin 3)).Adj w u := by
  simp only [ExistsUnique, completeGraph, top_adj]
  decide

end Frontier

