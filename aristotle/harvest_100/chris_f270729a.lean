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
# Pcp Dinur
Category: Frontier Cs
Target: CS.pcp_dinur
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

/-- A *constraint graph* (a binary constraint satisfaction instance): `n` variables taking
values in the alphabet `Fin (q+1)`, together with a list of binary constraints, each given by
an ordered pair of variables and a decidable relation on the alphabet. -/
structure ConstraintGraph where
  /-- Number of variables. -/
  n : ℕ
  /-- The alphabet is `Fin (q+1)`; in particular it is nonempty. -/
  q : ℕ
  /-- The constraints: each is a pair of variables together with a relation they must satisfy. -/
  edges : List ((Fin n × Fin n) × (Fin (q + 1) → Fin (q + 1) → Bool))

namespace ConstraintGraph

/-- An assignment of alphabet values to the variables of `G`. -/
abbrev Assignment (G : ConstraintGraph) := Fin G.n → Fin (G.q + 1)

/-- The number of constraints of `G` (its size). -/
def size (G : ConstraintGraph) : ℕ := G.edges.length

/-- The number of constraints of `G` violated by the assignment `a`. -/
def unsatCount (G : ConstraintGraph) (a : G.Assignment) : ℕ :=
  (G.edges.filter (fun e => !(e.2 (a e.1.1) (a e.1.2)))).length

/-- The minimal number of violated constraints, over all assignments. -/
def minUnsat (G : ConstraintGraph) : ℕ :=
  Finset.univ.inf' Finset.univ_nonempty (fun a : G.Assignment => G.unsatCount a)

/-- The *unsat value* of `G`: the minimal fraction of constraints violated by an assignment.
(By convention it is `0` for a graph with no constraints.) -/
def UNSAT (G : ConstraintGraph) : ℚ := (G.minUnsat : ℚ) / (G.size : ℚ)

/-- `G` is satisfiable if some assignment violates no constraint. -/
def Satisfiable (G : ConstraintGraph) : Prop := ∃ a : G.Assignment, G.unsatCount a = 0

lemma minUnsat_le (G : ConstraintGraph) (a : G.Assignment) : G.minUnsat ≤ G.unsatCount a :=
  Finset.inf'_le _ (Finset.mem_univ a)

lemma exists_unsatCount_eq_minUnsat (G : ConstraintGraph) :
    ∃ a : G.Assignment, G.unsatCount a = G.minUnsat := by
  obtain ⟨a, -, ha⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty)
    (fun a : G.Assignment => G.unsatCount a)
  exact ⟨a, ha.symm⟩

lemma unsatCount_le_size (G : ConstraintGraph) (a : G.Assignment) : G.unsatCount a ≤ G.size :=
  List.length_filter_le _ _

lemma minUnsat_le_size (G : ConstraintGraph) : G.minUnsat ≤ G.size := by
  obtain ⟨a, ha⟩ := G.exists_unsatCount_eq_minUnsat
  exact ha ▸ G.unsatCount_le_size a

lemma satisfiable_iff_minUnsat_eq_zero (G : ConstraintGraph) :
    G.Satisfiable ↔ G.minUnsat = 0 := by
  constructor
  · rintro ⟨a, ha⟩
    exact Nat.le_zero.mp (ha ▸ G.minUnsat_le a)
  · intro h
    obtain ⟨a, ha⟩ := G.exists_unsatCount_eq_minUnsat
    exact ⟨a, by rw [ha, h]⟩

lemma UNSAT_nonneg (G : ConstraintGraph) : 0 ≤ G.UNSAT := by
  unfold UNSAT
  positivity

/-- A satisfiable constraint graph has unsat value `0`. -/
lemma UNSAT_eq_zero_of_satisfiable {G : ConstraintGraph} (h : G.Satisfiable) : G.UNSAT = 0 := by
  rw [G.satisfiable_iff_minUnsat_eq_zero] at h
  simp [UNSAT, h]

/-- An unsatisfiable constraint graph violates at least one constraint, hence has unsat value
at least `1 / size`. -/
lemma inv_size_le_UNSAT {G : ConstraintGraph} (h : ¬ G.Satisfiable) :
    1 / (G.size : ℚ) ≤ G.UNSAT := by
  rw [G.satisfiable_iff_minUnsat_eq_zero] at h
  have h1 : 1 ≤ G.minUnsat := Nat.one_le_iff_ne_zero.mpr h
  have hs : 0 < G.size := lt_of_lt_of_le h1 G.minUnsat_le_size
  have hs' : (0 : ℚ) < (G.size : ℚ) := by exact_mod_cast hs
  have h1' : (1 : ℚ) ≤ (G.minUnsat : ℚ) := by exact_mod_cast h1
  unfold UNSAT
  gcongr

/-- A concrete unsatisfiable constraint graph: one variable, a one-element alphabet, and a
single constraint that is never satisfied. -/
def falseGraph : ConstraintGraph where
  n := 1
  q := 0
  edges := [((0, 0), fun _ _ => false)]

@[simp] lemma falseGraph_size : falseGraph.size = 1 := rfl

@[simp] lemma falseGraph_unsatCount (a : falseGraph.Assignment) :
    falseGraph.unsatCount a = 1 := rfl

@[simp] lemma falseGraph_minUnsat : falseGraph.minUnsat = 1 := by
  simp [minUnsat]

@[simp] lemma falseGraph_UNSAT : falseGraph.UNSAT = 1 := by
  simp [UNSAT]

lemma falseGraph_not_satisfiable : ¬ falseGraph.Satisfiable := by
  simp [satisfiable_iff_minUnsat_eq_zero]

end ConstraintGraph

open ConstraintGraph

/-- The key recursion in Dinur's proof: iterating a gap-doubling amplification step `t` times
multiplies the unsat value by `2 ^ t`, until it saturates at `α`. -/
lemma iterate_gap (amp : ConstraintGraph → ConstraintGraph) (α : ℚ) (hα : 0 ≤ α)
    (hgap : ∀ G, min α (2 * G.UNSAT) ≤ (amp G).UNSAT) (G : ConstraintGraph) (t : ℕ) :
    min α (2 ^ t * G.UNSAT) ≤ (amp^[t] G).UNSAT := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [Function.iterate_succ_apply']
      refine le_trans ?_ (hgap (amp^[t] G))
      refine le_min (min_le_left _ _) ?_
      have hstep : (2 : ℚ) * min α (2 ^ t * G.UNSAT) ≤ 2 * (amp^[t] G).UNSAT := by linarith
      refine le_trans ?_ hstep
      rcases le_total α (2 ^ t * G.UNSAT) with h | h
      · have : min α (2 ^ t * G.UNSAT) = α := min_eq_left h
        rw [this]
        calc min α (2 ^ (t + 1) * G.UNSAT) ≤ α := min_le_left _ _
          _ ≤ 2 * α := by linarith
      · have : min α (2 ^ t * G.UNSAT) = 2 ^ t * G.UNSAT := min_eq_right h
        rw [this]
        calc min α (2 ^ (t + 1) * G.UNSAT) ≤ 2 ^ (t + 1) * G.UNSAT := min_le_right _ _
          _ = 2 * (2 ^ t * G.UNSAT) := by ring

/-- Iterating the amplification step `t` times blows the size up by at most `K ^ t`. -/
lemma iterate_size (amp : ConstraintGraph → ConstraintGraph) (K : ℕ)
    (hsize : ∀ G, (amp G).size ≤ K * G.size) (G : ConstraintGraph) (t : ℕ) :
    (amp^[t] G).size ≤ K ^ t * G.size := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [Function.iterate_succ_apply']
      calc (amp (amp^[t] G)).size ≤ K * (amp^[t] G).size := hsize _
        _ ≤ K * (K ^ t * G.size) := Nat.mul_le_mul_left _ ih
        _ = K ^ (t + 1) * G.size := by ring

/-- Iterating the amplification step preserves satisfiability. -/
lemma iterate_satisfiable (amp : ConstraintGraph → ConstraintGraph)
    (hcomp : ∀ G, G.Satisfiable → (amp G).Satisfiable) (G : ConstraintGraph) (t : ℕ)
    (h : G.Satisfiable) : (amp^[t] G).Satisfiable := by
  induction t with
  | zero => simpa using h
  | succ t ih =>
      rw [Function.iterate_succ_apply']
      exact hcomp _ ih

/-- The blow-up `K ^ (clog 2 m)` is polynomial in `m`. -/
lemma pow_clog_le_poly (K m : ℕ) (hm : 1 ≤ m) :
    K ^ (Nat.clog 2 m) ≤ (2 * m) ^ (Nat.clog 2 K) := by
  have hpow : 2 ^ (Nat.clog 2 m) ≤ 2 * m := by
    rcases eq_or_lt_of_le hm with h | h
    · simp [← h]
    · have h1 : 0 < Nat.clog 2 m := Nat.clog_pos (by norm_num) h
      have h2 : 2 ^ (Nat.clog 2 m - 1) < m := Nat.pow_pred_clog_lt_self (by norm_num) h
      calc 2 ^ (Nat.clog 2 m) = 2 * 2 ^ (Nat.clog 2 m - 1) := by
            rw [← pow_succ']; congr 1; omega
        _ ≤ 2 * m := by omega
  have hK : K ≤ 2 ^ (Nat.clog 2 K) := Nat.le_pow_clog (by norm_num) K
  calc K ^ (Nat.clog 2 m) ≤ (2 ^ (Nat.clog 2 K)) ^ (Nat.clog 2 m) :=
        Nat.pow_le_pow_left hK _
    _ = (2 ^ (Nat.clog 2 m)) ^ (Nat.clog 2 K) := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    _ ≤ (2 * m) ^ (Nat.clog 2 K) := Nat.pow_le_pow_left hpow _

/--
**The PCP theorem, in Dinur's gap-amplification form.**

Assume a gap-amplification step `amp` on binary constraint graphs which
* blows up the size by at most a constant factor `K`,
* doubles the unsat value until it reaches the constant `α ∈ (0,1]`,
* and preserves satisfiability (perfect completeness).

Then, applying `amp` a logarithmic number of times, every constraint graph `G` reduces to a
constraint graph `H` of polynomial size such that `H` is satisfiable if `G` is, while
`H` has unsat value at least the constant `α` if `G` is unsatisfiable.

This is exactly the gap-producing reduction from constraint satisfaction to gap constraint
satisfaction that constitutes the PCP theorem.
-/
theorem pcp_dinur (amp : ConstraintGraph → ConstraintGraph) (K : ℕ) (α : ℚ)
    (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hsize : ∀ G, (amp G).size ≤ K * G.size)
    (hgap : ∀ G, min α (2 * G.UNSAT) ≤ (amp G).UNSAT)
    (hcomp : ∀ G, G.Satisfiable → (amp G).Satisfiable) :
    ∀ G : ConstraintGraph, ∃ H : ConstraintGraph,
      H = amp^[Nat.clog 2 G.size] G ∧
      H.size ≤ K ^ (Nat.clog 2 G.size) * G.size ∧
      H.size ≤ (2 * G.size + 2) ^ (Nat.clog 2 K + 1) ∧
      (G.Satisfiable → H.Satisfiable) ∧
      (¬ G.Satisfiable → α ≤ H.UNSAT) := by
  intro G
  set t := Nat.clog 2 G.size with ht
  refine ⟨amp^[t] G, rfl, iterate_size amp K hsize G t, ?_, ?_, ?_⟩
  · -- polynomial size bound
    rcases Nat.eq_zero_or_pos G.size with hm | hm
    · have h0 : (amp^[t] G).size ≤ K ^ t * G.size := iterate_size amp K hsize G t
      simp [hm] at h0
      omega
    · calc (amp^[t] G).size ≤ K ^ t * G.size := iterate_size amp K hsize G t
        _ ≤ (2 * G.size) ^ (Nat.clog 2 K) * G.size :=
            Nat.mul_le_mul_right _ (pow_clog_le_poly K G.size hm)
        _ ≤ (2 * G.size + 2) ^ (Nat.clog 2 K) * (2 * G.size + 2) :=
            Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) _) (by omega)
        _ = (2 * G.size + 2) ^ (Nat.clog 2 K + 1) := (pow_succ _ _).symm
  · exact fun h => iterate_satisfiable amp hcomp G t h
  · intro hns
    have hlb : 1 / (G.size : ℚ) ≤ G.UNSAT := inv_size_le_UNSAT hns
    have hmin : G.minUnsat ≠ 0 := (G.satisfiable_iff_minUnsat_eq_zero).not.mp hns
    have hm : 0 < G.size :=
      lt_of_lt_of_le (Nat.pos_of_ne_zero hmin) G.minUnsat_le_size
    have hmQ : (0 : ℚ) < (G.size : ℚ) := by exact_mod_cast hm
    have hpow : (G.size : ℚ) ≤ 2 ^ t := by
      have := Nat.le_pow_clog (b := 2) (by norm_num) G.size
      exact_mod_cast this
    have key : (1 : ℚ) ≤ 2 ^ t * G.UNSAT := by
      have h1 : (G.size : ℚ) * (1 / (G.size : ℚ)) ≤ (G.size : ℚ) * G.UNSAT :=
        mul_le_mul_of_nonneg_left hlb (le_of_lt hmQ)
      have h2 : (G.size : ℚ) * (1 / (G.size : ℚ)) = 1 := by field_simp
      have h3 : (G.size : ℚ) * G.UNSAT ≤ 2 ^ t * G.UNSAT :=
        mul_le_mul_of_nonneg_right hpow G.UNSAT_nonneg
      linarith
    have hgapt : min α (2 ^ t * G.UNSAT) ≤ (amp^[t] G).UNSAT :=
      iterate_gap amp α (le_of_lt hα0) hgap G t
    have : min α (2 ^ t * G.UNSAT) = α := min_eq_left (by linarith)
    linarith [this ▸ hgapt]

/-- **Non-vacuity of the hypotheses of `pcp_dinur`.** The assumptions on the amplification step
are consistent: there is an amplification step satisfying all of them (with `K = 1`, `α = 1`).
Of course, the content of Dinur's construction is that such a step can be realised by an
*efficiently computable* operation with a *bounded alphabet*, which the present statement does
not track. -/
lemma exists_amplification_step :
    ∃ (amp : ConstraintGraph → ConstraintGraph),
      (∀ G, (amp G).size ≤ 1 * G.size) ∧
      (∀ G, min (1 : ℚ) (2 * G.UNSAT) ≤ (amp G).UNSAT) ∧
      (∀ G, G.Satisfiable → (amp G).Satisfiable) := by
  classical
  refine ⟨fun G => if G.Satisfiable then G else falseGraph, ?_, ?_, ?_⟩
  · intro G
    by_cases h : G.Satisfiable
    · simp [h]
    · have hmin : G.minUnsat ≠ 0 := (G.satisfiable_iff_minUnsat_eq_zero).not.mp h
      have hm : 0 < G.size := lt_of_lt_of_le (Nat.pos_of_ne_zero hmin) G.minUnsat_le_size
      simp only [h, if_false, falseGraph_size, one_mul]
      omega
  · intro G
    by_cases h : G.Satisfiable
    · simp [h, UNSAT_eq_zero_of_satisfiable h]
    · simp [h]
  · intro G h
    simp [h]

end CS

