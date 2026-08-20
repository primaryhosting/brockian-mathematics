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

theorem accepts_of_sat {M : NTM} (hM : M.WF) {N T : ℕ} (hN : 0 < N) {x : ℕ → ℕ}
    (hx : ∀ i, x i < M.nSymbols) {σ : ℕ → Bool} (hsat : cnfEval σ (tableau M N T x) = true) :
    M.AcceptsIn N T x := by
  have hall : ∀ c ∈ tableau M N T x, clauseEval σ c = true := cnfEval_eq_true.1 hsat
  set bs : ℕ → Bool := fun t => σ (vChoice t) with hbs
  set R : ℕ → Config := M.run N (M.initConfig x) bs with hRdef
  have hrange : ∀ t, (R t).InRange M N := fun t =>
    NTM.run_inRange hM ⟨hM.start_lt, hN, hx⟩ bs t
  have hstep : ∀ t, R (t + 1) = M.step N (R t) (bs t) := fun t => rfl
  -- "at least one" facts
  have symSome : ∀ t ≤ T, ∀ i < N, ∃ s, s < M.nSymbols ∧ σ (vSym M N t i s) = true := by
    intro t ht i hi
    have h := hall _ (gSymSome_sub (mem_gSymSome ht hi))
    rw [clauseEval_eq_true] at h
    obtain ⟨l, hl, hlv⟩ := h
    simp only [List.mem_map, List.mem_range] at hl
    obtain ⟨s, hs, rfl⟩ := hl
    exact ⟨s, hs, by simpa [litEval] using hlv⟩
  have stateSome : ∀ t ≤ T, ∃ q, q < M.nStates ∧ σ (vState M t q) = true := by
    intro t ht
    have h := hall _ (gStateSome_sub (mem_gStateSome (M := M) ht))
    rw [clauseEval_eq_true] at h
    obtain ⟨l, hl, hlv⟩ := h
    simp only [List.mem_map, List.mem_range] at hl
    obtain ⟨q, hq, rfl⟩ := hl
    exact ⟨q, hq, by simpa [litEval] using hlv⟩
  have headSome : ∀ t ≤ T, ∃ i, i < N ∧ σ (vHead N t i) = true := by
    intro t ht
    have h := hall _ (gHeadSome_sub (M := M) (x := x) (mem_gHeadSome (N := N) ht))
    rw [clauseEval_eq_true] at h
    obtain ⟨l, hl, hlv⟩ := h
    simp only [List.mem_map, List.mem_range] at hl
    obtain ⟨i, hi, rfl⟩ := hl
    exact ⟨i, hi, by simpa [litEval] using hlv⟩
  -- "at most one" facts
  have symUniq : ∀ t ≤ T, ∀ i < N, ∀ s < M.nSymbols, ∀ s' < M.nSymbols,
      σ (vSym M N t i s) = true → σ (vSym M N t i s') = true → s = s' := by
    intro t ht i hi s hs s' hs' h h'
    rcases lt_trichotomy s s' with hlt | heq | hgt
    · have hc := hall _ (gSymUnique_sub (mem_gSymUnique ht hi hs' hlt))
      rw [clauseEval_eq_true] at hc
      obtain ⟨l, hl, hlv⟩ := hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl <;> simp [litEval, h, h'] at hlv
    · exact heq
    · have hc := hall _ (gSymUnique_sub (mem_gSymUnique ht hi hs hgt))
      rw [clauseEval_eq_true] at hc
      obtain ⟨l, hl, hlv⟩ := hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl <;> simp [litEval, h, h'] at hlv
  have stateUniq : ∀ t ≤ T, ∀ q < M.nStates, ∀ q' < M.nStates,
      σ (vState M t q) = true → σ (vState M t q') = true → q = q' := by
    intro t ht q hq q' hq' h h'
    rcases lt_trichotomy q q' with hlt | heq | hgt
    · have hc := hall _ (gStateUnique_sub (mem_gStateUnique ht hq' hlt))
      rw [clauseEval_eq_true] at hc
      obtain ⟨l, hl, hlv⟩ := hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl <;> simp [litEval, h, h'] at hlv
    · exact heq
    · have hc := hall _ (gStateUnique_sub (mem_gStateUnique ht hq hgt))
      rw [clauseEval_eq_true] at hc
      obtain ⟨l, hl, hlv⟩ := hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl <;> simp [litEval, h, h'] at hlv
  have headUniq : ∀ t ≤ T, ∀ i < N, ∀ i' < N,
      σ (vHead N t i) = true → σ (vHead N t i') = true → i = i' := by
    intro t ht i hi i' hi' h h'
    rcases lt_trichotomy i i' with hlt | heq | hgt
    · have hc := hall _ (gHeadUnique_sub (M := M) (x := x) (mem_gHeadUnique ht hi' hlt))
      rw [clauseEval_eq_true] at hc
      obtain ⟨l, hl, hlv⟩ := hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl <;> simp [litEval, h, h'] at hlv
    · exact heq
    · have hc := hall _ (gHeadUnique_sub (M := M) (x := x) (mem_gHeadUnique ht hi hgt))
      rw [clauseEval_eq_true] at hc
      obtain ⟨l, hl, hlv⟩ := hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl <;> simp [litEval, h, h'] at hlv
  -- the main induction
  have key : ∀ t, t ≤ T →
      (∀ q, q < M.nStates → σ (vState M t q) = true → q = (R t).state) ∧
      (∀ i, i < N → σ (vHead N t i) = true → i = (R t).head) ∧
      (∀ i, i < N → ∀ s, s < M.nSymbols → σ (vSym M N t i s) = true → s = (R t).tape i) := by
    intro t
    induction t with
    | zero =>
      intro _
      have h0 : R 0 = M.initConfig x := rfl
      have hst : σ (vState M 0 M.start) = true := by
        have hmem : [(⟨vState M 0 M.start, true⟩ : Lit)] ∈ gInit M N x := by simp [gInit]
        have hc := hall _ (gInit_sub (T := T) hmem)
        simpa [clauseEval, litEval] using hc
      have hhd : σ (vHead N 0 0) = true := by
        have hmem : [(⟨vHead N 0 0, true⟩ : Lit)] ∈ gInit M N x := by simp [gInit]
        have hc := hall _ (gInit_sub (T := T) hmem)
        simpa [clauseEval, litEval] using hc
      refine ⟨?_, ?_, ?_⟩
      · intro q hq h
        rw [h0]
        exact stateUniq 0 (Nat.zero_le _) q hq _ hM.start_lt h hst
      · intro i hi h
        rw [h0]
        exact headUniq 0 (Nat.zero_le _) i hi 0 hN h hhd
      · intro i hi s hs h
        have hmem : [(⟨vSym M N 0 i (x i), true⟩ : Lit)] ∈ gInit M N x := by
          simp only [gInit, List.mem_cons, List.mem_map, List.mem_range]
          exact Or.inr (Or.inr ⟨i, hi, rfl⟩)
        have hc := hall _ (gInit_sub (T := T) hmem)
        have hxi : σ (vSym M N 0 i (x i)) = true := by simpa [clauseEval, litEval] using hc
        rw [h0]
        exact symUniq 0 (Nat.zero_le _) i hi s hs _ (hx i) h hxi
    | succ t ih =>
      intro ht1
      have ht : t < T := by omega
      have htle : t ≤ T := by omega
      obtain ⟨ihq, ihh, ihs⟩ := ih htle
      -- the true state/head/symbol at time `t` are asserted by the assignment
      have posQ : σ (vState M t (R t).state) = true := by
        obtain ⟨q, hq, hqv⟩ := stateSome t htle
        rwa [ihq q hq hqv] at hqv
      have posH : σ (vHead N t (R t).head) = true := by
        obtain ⟨i, hi, hiv⟩ := headSome t htle
        rwa [ihh i hi hiv] at hiv
      have posS : ∀ i, i < N → σ (vSym M N t i ((R t).tape i)) = true := by
        intro i hi
        obtain ⟨s, hs, hsv⟩ := symSome t htle i hi
        rwa [ihs i hi s hs hsv] at hsv
      have hpremfalse :
          clauseEval σ (transPrem M N t (R t).head (R t).state ((R t).tape (R t).head) (bs t))
            = false := by
        have hch : σ (vChoice t) = bs t := rfl
        cases hb : bs t <;>
          simp [clauseEval, transPrem, litEval, posQ, posH, posS _ (hrange t).head_lt, hch, hb]
      have hi0 : (R t).head < N := (hrange t).head_lt
      have hq0 : (R t).state < M.nStates := (hrange t).state_lt
      have hs0 : (R t).tape (R t).head < M.nSymbols := (hrange t).tape_lt _
      have hR1 : R (t + 1) = M.step N (R t) (bs t) := hstep t
      -- the three conclusions of the transition clauses
      have c1 : σ (vState M (t + 1) (R (t + 1)).state) = true := by
        have hc := hall _ (gTrans_sub (x := x) (mem_gTrans (b := bs t) ht hi0 hq0 hs0 (Or.inl rfl)))
        have := litEval_of_append hc hpremfalse
        rw [hR1]
        simpa [litEval, NTM.step] using this
      have c2 : σ (vSym M N (t + 1) (R t).head ((R (t + 1)).tape (R t).head)) = true := by
        have hc := hall _ (gTrans_sub (x := x) (mem_gTrans (b := bs t) ht hi0 hq0 hs0 (Or.inr (Or.inl rfl))))
        have := litEval_of_append hc hpremfalse
        rw [hR1]
        simpa [litEval, NTM.step] using this
      have c3 : σ (vHead N (t + 1) (R (t + 1)).head) = true := by
        have hc := hall _
          (gTrans_sub (x := x) (mem_gTrans (b := bs t) ht hi0 hq0 hs0 (Or.inr (Or.inr rfl))))
        have := litEval_of_append hc hpremfalse
        rw [hR1]
        simpa [litEval, NTM.step] using this
      have hstate1 : (R (t + 1)).state < M.nStates := (hrange (t + 1)).state_lt
      have hhead1 : (R (t + 1)).head < N := (hrange (t + 1)).head_lt
      refine ⟨?_, ?_, ?_⟩
      · intro q hq h
        exact stateUniq (t + 1) ht1 q hq _ hstate1 h c1
      · intro i hi h
        exact headUniq (t + 1) ht1 i hi _ hhead1 h c3
      · intro i hi s hs h
        by_cases hie : i = (R t).head
        · subst hie
          exact symUniq (t + 1) ht1 _ hi s hs _ ((hrange (t + 1)).tape_lt _) h c2
        · have hne : σ (vHead N t i) = false := by
            by_contra hcon
            exact hie (ihh i hi (by simpa using hcon))
          have hc := hall _ (gInertia_sub (x := x) (mem_gInertia ht hi ((hrange t).tape_lt i)))
          rw [clauseEval_eq_true] at hc
          obtain ⟨l, hl, hlv⟩ := hc
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
          have hkeep : σ (vSym M N (t + 1) i ((R t).tape i)) = true := by
            rcases hl with rfl | rfl | rfl
            · simp [litEval, hne] at hlv
            · simp [litEval, posS i hi] at hlv
            · simpa [litEval] using hlv
          have htape : (R (t + 1)).tape i = (R t).tape i := by
            rw [hR1]; simp [NTM.step, hie]
          rw [htape]
          exact symUniq (t + 1) ht1 i hi s hs _ ((hrange t).tape_lt i) h hkeep
  -- conclude from the accepting clause
  refine ⟨bs, ?_⟩
  have hmemacc : [(⟨vState M T M.accept, true⟩ : Lit)] ∈ gAccept M T := by simp [gAccept]
  have hc := hall _ (gAccept_sub (N := N) (x := x) hmemacc)
  have hacc : σ (vState M T M.accept) = true := by simpa [clauseEval, litEval] using hc
  exact ((key T le_rfl).1 M.accept hM.accept_lt hacc).symm

/-! ## The main equivalence -/

/-- **The Cook–Levin tableau theorem.**  The explicitly constructed CNF formula
`tableau M N T x` is satisfiable if and only if the nondeterministic machine `M`,
run on the tape `x` with `N` cells, has an accepting computation of length `T`. -/
