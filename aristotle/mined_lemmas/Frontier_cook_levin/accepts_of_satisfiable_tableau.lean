/-
# Cook Levin
Category: Frontier — Moonshot
Target: Frontier.cook_levin
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean 4.28 does not allow a module docstring before the import block, so this header
is a plain block comment; the text is otherwise verbatim.)
-/

import Mathlib
import RequestProject.CookLevin.Sat
import RequestProject.CookLevin.Machine
import RequestProject.CookLevin.Tableau
import RequestProject.CookLevin.Forward
import RequestProject.CookLevin.Backward
import RequestProject.CookLevin.Size
import RequestProject.CookLevin.Sanity
import RequestProject.CookLevin.Certificate

/-!
## The Cook–Levin theorem

`Frontier.cook_levin` states that SAT is `NP`-hard: every language `L` in `NP` is reduced to
`SATLang`, the set of satisfiable CNF formulas over `ℕ`, by the explicit computable map
`Frontier.reduction`, whose output is of polynomial size.

The complexity class `NP` is modelled by single-tape nondeterministic Turing machines
(`Frontier.NTM`) with a polynomial time bound (`Frontier.InNP`), and the reduction is the
classical *tableau* construction: `Frontier.tableau M x T` is a CNF formula whose satisfying
assignments are exactly the accepting computations of `M` on `x` of length `T`
(`Frontier.tableau_satisfiable_iff`).

### Sources and scope

* Mathlib (at the version pinned by this project) contains no complexity theory: there is no
  definition of `P`, `NP`, of polynomial-time reductions, or of SAT, and no Cook–Levin
  statement.  Everything below is therefore developed from scratch, except for the CNF
  datatype `Std.Sat.CNF` and its relabelling API, which come from the Lean core library.
* What is proved is the hard half of the Cook–Levin theorem, `NP`-hardness of SAT, for
  many-one reductions that are computable Lean functions of polynomially bounded output
  size.  Two ingredients of the textbook statement are *not* formalised here: that the
  reduction runs in polynomial *time* (this project fixes no cost model for computing the
  reduction itself), and the easy half `SAT ∈ NP` (which would require programming and
  verifying a nondeterministic Turing machine that parses and evaluates encoded formulas).
  `Frontier.satisfiable_iff_exists_certificate` records the certificate characterisation of
  satisfiability that underlies the easy half.
-/

namespace Frontier

open Std.Sat

/-! ### Encoding the tableau variables by natural numbers -/

/-- Numerical code of a tape symbol. -/

theorem accepts_of_satisfiable_tableau (h : Satisfiable (tableau M x T)) : M.Accepts x T := by
  obtain ⟨σ, hσ⟩ := h
  rw [eval_tableau_iff, eval_stateClauses_iff, eval_headClauses_iff, eval_cellClauses_iff,
    eval_initClauses_iff, eval_acceptClauses_iff, eval_headBoundClauses_iff,
    eval_transClauses_iff, eval_inertiaClauses_iff] at hσ
  obtain ⟨hst, hhd, hce, ⟨hin1, hin2, hin3⟩, hacc, hhb, ⟨htr1, htr2⟩, hinert⟩ := hσ
  -- the state, head and cell functions determined by `σ`
  have hSspec : ∀ t ≤ T, stateAt M σ t < M.numStates ∧ σ (TVar.st t (stateAt M σ t)) = true :=
    fun t ht => stateAt_spec (hst t ht).1
  have hSuniq : ∀ t ≤ T, ∀ q < M.numStates, σ (TVar.st t q) = true → q = stateAt M σ t :=
    fun t ht q hq hq' => (hst t ht).2 q hq _ (hSspec t ht).1 hq' (hSspec t ht).2
  have hHspec : ∀ t ≤ T, headAt T σ t ≤ T ∧ σ (TVar.hd t (headAt T σ t)) = true :=
    fun t ht => headAt_spec (hhd t ht).1
  have hHuniq : ∀ t ≤ T, ∀ i ≤ T, σ (TVar.hd t i) = true → i = headAt T σ t :=
    fun t ht i hi hi' => (hhd t ht).2 i hi _ (hHspec t ht).1 hi' (hHspec t ht).2
  have hCspec : ∀ t ≤ T, ∀ i ≤ T, σ (TVar.cell t i (cellAt σ t i)) = true :=
    fun t ht i hi => cellAt_spec (hce t ht i hi).1
  have hCuniq : ∀ t ≤ T, ∀ i ≤ T, ∀ a : Sym, σ (TVar.cell t i a) = true → a = cellAt σ t i :=
    fun t ht i hi a ha => (hce t ht i hi).2 a _ ha (hCspec t ht i hi)
  refine ⟨fun t => ⟨stateAt M σ (min t T),
      fun i => if i ≤ T then cellAt σ (min t T) i else x[i]?, headAt T σ (min t T)⟩, ?_, ?_, ?_⟩
  · -- the initial configuration
    have h0 : min 0 T = 0 := Nat.zero_min T
    simp only [h0, NTM.init, Cfg.mk.injEq]
    refine ⟨(hSuniq 0 (Nat.zero_le T) M.start M.start_lt hin1).symm, ?_,
      (hHuniq 0 (Nat.zero_le T) 0 (Nat.zero_le T) hin2).symm⟩
    funext i
    by_cases hi : i ≤ T
    · simp only [hi, if_pos]
      exact (hCuniq 0 (Nat.zero_le T) i hi _ (hin3 i hi)).symm
    · simp [hi]
  · -- the transition steps
    intro t ht
    have htT : min t T = t := min_eq_left (le_of_lt ht)
    have ht1T : min (t + 1) T = t + 1 := min_eq_left ht
    obtain ⟨j, hj, hmv⟩ := htr1 t ht
    obtain ⟨hq, hq', hrest⟩ := htr2 t ht j hj hmv
    have htrmem : M.trAt j ∈ M.transList := M.trAt_mem hj
    rw [NTM.mem_transList] at htrmem
    obtain ⟨hqlt, hstepmem⟩ := htrmem
    have hq'lt : (M.trAt j).q' < M.numStates := M.step_lt _ _ _ hstepmem
    -- the head position at time `t`
    set i := headAt T σ t with hi
    have hiT : i ≤ T := (hHspec t (le_of_lt ht)).1
    have hiσ : σ (TVar.hd t i) = true := (hHspec t (le_of_lt ht)).2
    have hiltT : i < T := by
      rcases lt_or_eq_of_le hiT with h | h
      · exact h
      · rw [h] at hiσ
        rw [hhb t ht] at hiσ
        exact absurd hiσ (by simp)
    obtain ⟨hca, hca', hcd⟩ := hrest i hiT hiσ
    have hSq : (M.trAt j).q = stateAt M σ t := hSuniq t (le_of_lt ht) _ hqlt hq
    have hSq' : (M.trAt j).q' = stateAt M σ (t + 1) := hSuniq (t + 1) ht _ hq'lt hq'
    have hCa : (M.trAt j).a = cellAt σ t i := hCuniq t (le_of_lt ht) i hiT _ hca
    have hCa' : (M.trAt j).a' = cellAt σ (t + 1) i := hCuniq (t + 1) ht i hiT _ hca'
    have hmoveT : (M.trAt j).d.move i ≤ T := le_trans ((M.trAt j).d.move_le i) hiltT
    have hHd' : (M.trAt j).d.move i = headAt T σ (t + 1) :=
      hHuniq (t + 1) ht _ hmoveT hcd
    refine ⟨(M.trAt j).d, ?_, ?_, ?_⟩
    · simp only [htT, ht1T, hiT, if_pos, ← hi]
      rw [← hSq, ← hSq', ← hCa, ← hCa']
      · exact hstepmem
    · simp only [htT, ht1T, ← hi]
      rw [← hHd']
    · intro k hk
      simp only [htT, ht1T, ← hi] at hk ⊢
      by_cases hkT : k ≤ T
      · simp only [hkT, if_pos]
        exact (hCuniq (t + 1) ht k hkT _
          (hinert t ht i hiT k hkT hk _ hiσ (hCspec t (le_of_lt ht) k hkT))).symm
      · simp [hkT]
  · -- the accepting time
    obtain ⟨t, htT, hσt⟩ := hacc
    refine ⟨t, htT, ?_⟩
    simp only [min_eq_left htT]
    exact (hSuniq t htT M.accept M.accept_lt hσt).symm

end Frontier

/-
Basic SAT vocabulary, built on the `Std.Sat.CNF` datatype from the Lean core library.
-/
import Mathlib
import Std.Sat.CNF.Relabel

namespace Frontier

open Std.Sat

/-- A CNF formula is satisfiable if some assignment evaluates it to `true`. -/
