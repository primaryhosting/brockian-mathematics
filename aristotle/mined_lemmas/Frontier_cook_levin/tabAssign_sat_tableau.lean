import RequestProject.Frontier.Basic
import RequestProject.Frontier.Tableau
import RequestProject.Frontier.Correctness
import RequestProject.Frontier.Size
import RequestProject.Frontier.NP

import Mathlib

/-!
# The Cook–Levin theorem (tableau reduction)

This file develops, from scratch, the core of the Cook–Levin theorem: the *tableau
reduction* from an arbitrary nondeterministic Turing machine computation to the
satisfiability of a CNF formula.

## Main results

* `Frontier.tableau_satisfiable_iff`: for a well-formed nondeterministic Turing machine
  `M` with a tape of `N` cells, a time bound `T` and an input tape `x`, the explicitly
  constructed CNF formula `Frontier.tableau M N T x` is satisfiable if and only if `M`
  has an accepting computation on `x` of length `T`.
* `Frontier.tableau_length_le`: the tableau has polynomially many clauses.
* `Frontier.cook_levin`: **SAT is NP-hard**.  Every language in `Frontier.InNP` (defined
  via nondeterministic Turing machines with a polynomially bounded running time) is
  many-one reducible to satisfiability of CNF formulas, by the explicit reduction
  `Frontier.satReduction`, whose output has polynomially bounded size.
* `Frontier.satisfiable_iff_exists_certificate`: the membership half, at the level of
  certificates — a formula is satisfiable exactly when it admits a certificate of
  length `maxVar φ + 1` accepted by the explicit checker `Frontier.checkSat`.

## Scope

The hardness half is proved in full, including the polynomial bound on the size of the
produced formula; the reduction itself is an explicit, executable function.  What is
*not* formalised here is a machine-level cost model for computing the reduction, nor a
Turing machine implementation of a SAT verifier; the membership half is formalised in
the certificate form described above rather than by exhibiting such a machine.
-/

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

import RequestProject.Frontier.Size

/-!
# SAT is NP-hard

Polynomially bounded functions, the class NP defined via nondeterministic Turing
machines, the Cook-Levin reduction, and the certificate characterisation of
satisfiability.
-/

namespace Frontier

/-! ## SAT is NP-hard

We now package the tableau reduction as the statement that SAT is NP-hard.
A language over the binary alphabet is in NP when it is decided by a
nondeterministic Turing machine within a polynomially bounded number of steps. -/

/-- `f` is bounded by a polynomial. -/

theorem tabAssign_sat_tableau
    (hacc : (runOf M N x bs T).state = M.accept) :
    cnfEval (tabAssign M N (runOf M N x bs) bs) (tableau M N T x) = true := by
  set R := runOf M N x bs with hR
  set σ := tabAssign M N R bs with hσ
  have hrange : ∀ t, (R t).InRange M N := runOf_inRange hM hN hx bs
  have hstep : ∀ t, R (t + 1) = M.step N (R t) (bs t) := fun t => rfl
  -- values of the assignment
  have hsym : ∀ t i s, s < M.nSymbols → i < N → σ (vSym M N t i s) = decide (s = (R t).tape i) :=
    fun t i s hs hi => tabAssign_vSym hs hi
  have hstate : ∀ t q, q < M.nStates → σ (vState M t q) = decide (q = (R t).state) :=
    fun t q hq => tabAssign_vState hq
  have hhead : ∀ t i, i < N → σ (vHead N t i) = decide (i = (R t).head) :=
    fun t i hi => tabAssign_vHead hi
  have hch : ∀ t, σ (vChoice t) = bs t := fun t => tabAssign_vChoice
  -- premise analysis for the transition clauses
  have hprem : ∀ t i q s b, i < N → q < M.nStates → s < M.nSymbols →
      clauseEval σ (transPrem M N t i q s b) = true ∨
        (i = (R t).head ∧ q = (R t).state ∧ s = (R t).tape i ∧ bs t = b) := by
    intro t i q s b hi hq hs
    by_cases h1 : i = (R t).head
    · by_cases h2 : q = (R t).state
      · by_cases h3 : s = (R t).tape i
        · by_cases h4 : bs t = b
          · exact Or.inr ⟨h1, h2, h3, h4⟩
          · refine Or.inl ?_
            rw [clauseEval_eq_true]
            refine ⟨⟨vChoice t, !b⟩, by simp [transPrem], ?_⟩
            cases b <;> simp [litEval, hch] at h4 ⊢ <;> simp [h4]
        · refine Or.inl ?_
          rw [clauseEval_eq_true]
          exact ⟨⟨vSym M N t i s, false⟩, by simp [transPrem], by simp [litEval, hsym t i s hs hi, h3]⟩
      · refine Or.inl ?_
        rw [clauseEval_eq_true]
        exact ⟨⟨vState M t q, false⟩, by simp [transPrem], by simp [litEval, hstate t q hq, h2]⟩
    · refine Or.inl ?_
      rw [clauseEval_eq_true]
      exact ⟨⟨vHead N t i, false⟩, by simp [transPrem], by simp [litEval, hhead t i hi, h1]⟩
  have hconcl : ∀ (c : Clause) (l : Lit), litEval σ l = true → clauseEval σ (c ++ [l]) = true := by
    intro c l hl
    rw [clauseEval_eq_true]
    exact ⟨l, by simp, hl⟩
  rw [tableau]
  simp only [cnfEval_append, Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · -- gSymSome
    rw [cnfEval_eq_true]
    intro c hc
    simp only [gSymSome, List.mem_flatMap, List.mem_map, List.mem_range] at hc
    obtain ⟨t, ht, i, hi, rfl⟩ := hc
    rw [clauseEval_eq_true]
    refine ⟨⟨vSym M N t i ((R t).tape i), true⟩, ?_, ?_⟩
    · exact List.mem_map.2 ⟨(R t).tape i, List.mem_range.2 ((hrange t).tape_lt i), rfl⟩
    · simp [litEval, hsym t i _ ((hrange t).tape_lt i) hi]
  · -- gSymUnique
    rw [cnfEval_eq_true]
    intro c hc
    simp only [gSymUnique, List.mem_flatMap, List.mem_map, List.mem_range] at hc
    obtain ⟨t, ht, i, hi, s, hs, s', hs', rfl⟩ := hc
    rw [clauseEval_eq_true]
    by_cases h : s = (R t).tape i
    · refine ⟨⟨vSym M N t i s', false⟩, by simp, ?_⟩
      have hs'' : s' < M.nSymbols := by omega
      simp [litEval, hsym t i s' hs'' hi]
      omega
    · exact ⟨⟨vSym M N t i s, false⟩, by simp, by simp [litEval, hsym t i s hs hi, h]⟩
  · -- gStateSome
    rw [cnfEval_eq_true]
    intro c hc
    simp only [gStateSome, List.mem_map, List.mem_range] at hc
    obtain ⟨t, ht, rfl⟩ := hc
    rw [clauseEval_eq_true]
    refine ⟨⟨vState M t (R t).state, true⟩, ?_, ?_⟩
    · exact List.mem_map.2 ⟨(R t).state, List.mem_range.2 (hrange t).state_lt, rfl⟩
    · simp [litEval, hstate t _ (hrange t).state_lt]
  · -- gStateUnique
    rw [cnfEval_eq_true]
    intro c hc
    simp only [gStateUnique, List.mem_flatMap, List.mem_map, List.mem_range] at hc
    obtain ⟨t, ht, q, hq, q', hq', rfl⟩ := hc
    rw [clauseEval_eq_true]
    by_cases h : q = (R t).state
    · refine ⟨⟨vState M t q', false⟩, by simp, ?_⟩
      have hq'' : q' < M.nStates := by omega
      simp [litEval, hstate t q' hq'']
      omega
    · exact ⟨⟨vState M t q, false⟩, by simp, by simp [litEval, hstate t q hq, h]⟩
  · -- gHeadSome
    rw [cnfEval_eq_true]
    intro c hc
    simp only [gHeadSome, List.mem_map, List.mem_range] at hc
    obtain ⟨t, ht, rfl⟩ := hc
    rw [clauseEval_eq_true]
    refine ⟨⟨vHead N t (R t).head, true⟩, ?_, ?_⟩
    · exact List.mem_map.2 ⟨(R t).head, List.mem_range.2 (hrange t).head_lt, rfl⟩
    · simp [litEval, hhead t _ (hrange t).head_lt]
  · -- gHeadUnique
    rw [cnfEval_eq_true]
    intro c hc
    simp only [gHeadUnique, List.mem_flatMap, List.mem_map, List.mem_range] at hc
    obtain ⟨t, ht, i, hi, i', hi', rfl⟩ := hc
    rw [clauseEval_eq_true]
    by_cases h : i = (R t).head
    · refine ⟨⟨vHead N t i', false⟩, by simp, ?_⟩
      have hi'' : i' < N := by omega
      simp [litEval, hhead t i' hi'']
      omega
    · exact ⟨⟨vHead N t i, false⟩, by simp, by simp [litEval, hhead t i hi, h]⟩
  · -- gInit
    rw [cnfEval_eq_true]
    intro c hc
    simp only [gInit, List.mem_cons, List.mem_map, List.mem_range] at hc
    have h0 : R 0 = M.initConfig x := rfl
    rcases hc with rfl | rfl | ⟨i, hi, rfl⟩
    · rw [clauseEval_eq_true]
      refine ⟨⟨vState M 0 M.start, true⟩, by simp, ?_⟩
      rw [litEval_pos, hstate 0 _ hM.start_lt]
      simp [h0, NTM.initConfig]
    · rw [clauseEval_eq_true]
      refine ⟨⟨vHead N 0 0, true⟩, by simp, ?_⟩
      rw [litEval_pos, hhead 0 0 hN]
      simp [h0, NTM.initConfig]
    · rw [clauseEval_eq_true]
      refine ⟨⟨vSym M N 0 i (x i), true⟩, by simp, ?_⟩
      rw [litEval_pos, hsym 0 i _ (hx i) hi]
      simp [h0, NTM.initConfig]
  · -- gAccept
    rw [cnfEval_eq_true]
    intro c hc
    simp only [gAccept, List.mem_singleton] at hc
    subst hc
    rw [clauseEval_eq_true]
    refine ⟨⟨vState M T M.accept, true⟩, by simp, ?_⟩
    rw [litEval_pos, hstate T _ hM.accept_lt]
    simp [hacc]
  · -- gTrans
    rw [cnfEval_eq_true]
    intro c hc
    simp only [gTrans, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
      or_false] at hc
    obtain ⟨t, ht, i, hi, q, hq, s, hs, b, -, hcc⟩ := hc
    rcases hprem t i q s b hi hq hs with hp | ⟨e1, e2, e3, e4⟩
    · rcases hcc with rfl | rfl | rfl <;> simp [clauseEval_append, hp]
    · have hR1 : R (t + 1) = M.step N (R t) b := by rw [hstep t, e4]
      subst e1; subst e2; subst e3
      rcases hcc with rfl | rfl | rfl
      · refine hconcl _ _ ?_
        rw [litEval_pos, hstate _ _ (hM.δ_state_lt _ _ _), hR1]
        simp [NTM.step]
      · refine hconcl _ _ ?_
        rw [litEval_pos, hsym _ _ _ (hM.δ_symbol_lt _ _ _) hi, hR1]
        simp [NTM.step]
      · refine hconcl _ _ ?_
        rw [litEval_pos, hhead _ _ (moveHead_lt hi _), hR1]
        simp [NTM.step]
  · -- gInertia
    rw [cnfEval_eq_true]
    intro c hc
    simp only [gInertia, List.mem_flatMap, List.mem_map, List.mem_range] at hc
    obtain ⟨t, ht, i, hi, s, hs, rfl⟩ := hc
    rw [clauseEval_eq_true]
    by_cases h1 : i = (R t).head
    · refine ⟨⟨vHead N t i, true⟩, by simp, ?_⟩
      rw [litEval_pos, hhead t i hi]
      simp [h1]
    · by_cases h2 : s = (R t).tape i
      · refine ⟨⟨vSym M N (t + 1) i s, true⟩, by simp, ?_⟩
        rw [litEval_pos, hsym _ _ _ hs hi, hstep t]
        simp [NTM.step, h1, ← h2]
      · exact ⟨⟨vSym M N t i s, false⟩, by simp, by simp [litEval, hsym t i s hs hi, h2]⟩

end Complete

/-! ## Soundness: a satisfying assignment yields an accepting run -/

section Subsets

variable {M : NTM} {N T : ℕ} {x : ℕ → ℕ}

