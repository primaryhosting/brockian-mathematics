import Mathlib

/-!
# Cook Levin
Category: Frontier — Moonshot
Target: Frontier.cook_levin
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

/-!
## Overview

This file formalises the combinatorial core of the Cook–Levin theorem: *bounded
nondeterministic computation is reducible to Boolean satisfiability*.

The model of computation is a **sequential Boolean circuit machine**: a machine has a
configuration consisting of `width` bits, and one Boolean circuit (a straight-line
program of NAND gates, constants and reads of the current configuration) per output bit,
describing how the configuration is updated in one step.  Running the machine for `t`
steps from an initial configuration `c₀` and looking at the designated accepting bit
`acc` gives the acceptance predicate `Frontier.Accepts`.

Nondeterminism is the usual "guess" formulation: the input `x : List Bool` is written on
the first `x.length` bits of the initial configuration, and all remaining bits of the
initial configuration are unconstrained (they are the witness / nondeterministic guess).

The reduction `Frontier.tableau M x t` is the explicit computation tableau CNF:
a Boolean variable for every configuration bit at every time step, a Tseitin variable for
every gate of every step circuit at every time step, together with clauses forcing the
input bits, forcing the gate variables to compute the circuits, linking each layer to the
next, and asserting acceptance.

The main theorem `Frontier.cook_levin` says that `x` is accepted (for some witness) within
`t` steps **iff** the CNF `tableau M x t` is satisfiable, i.e. the explicit map
`x ↦ tableau M x (tb x.length)` is a many-one reduction of the language of `M` to `SAT`.
`Frontier.tableau_length_le` gives the accompanying size bound, which is polynomial
whenever the time bound, the width and the circuit sizes are polynomial; this is what
makes the reduction a polynomial-time (Karp) reduction.
-/

namespace Frontier

/-! ### CNF formulas -/

/-- An assignment of truth values to (natural-number indexed) Boolean variables. -/
abbrev Assign := ℕ → Bool

/-- A literal: a variable index together with the polarity that makes it true. -/
abbrev Lit := ℕ × Bool

/-- A clause is a disjunction of literals. -/
abbrev Clause := List Lit

/-- A CNF formula is a conjunction of clauses. -/
abbrev CNFFormula := List Clause

/-- A clause is satisfied by `σ` when one of its literals is true under `σ`. -/

private lemma sigma_gate (hσ : ∀ c ∈ tableau M x t, clauseSat σ c) {i j : ℕ}
    (hi : i < t) (hj : j < M.width)
    (hcfg : ∀ p, p < M.width → σ (vCfg i p) = conf M (c₀of σ) i p) :
    ∀ k, k < (M.step j).gates.length →
      σ (vGate i j k) = gateVal (M.step j).gates (mask M (conf M (c₀of σ) i)) k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    have hget : (M.step j).gates[k]? =
        some ((M.step j).gates.getD k (Gate.const false)) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
      simp
    have hin : ∀ c ∈ gateClauses M i j k ((M.step j).gates.getD k (Gate.const false)),
        clauseSat σ c := by
      intro c hc
      exact hσ _ (mem_tableau_step M x t hi hj (mem_stepClauses_gate M i j hk hc))
    have href : ∀ a, σ (vRef i j k a) =
        (if _h : a < k then gateVal (M.step j).gates (mask M (conf M (c₀of σ) i)) a
          else false) := by
      intro a
      by_cases ha : a < k
      · rw [vRef, if_pos ha, dif_pos ha]
        exact ih a ha (by omega)
      · rw [vRef, if_neg ha, dif_neg ha]
        exact sigma_false hσ
    cases hg : (M.step j).gates.getD k (Gate.const false) with
    | const b =>
        rw [hg] at hget
        have h := hin [(vGate i j k, b)] (by rw [hg]; simp [gateClauses])
        rw [clauseSat_one] at h
        rw [h, gateVal_const hget]
    | inp p =>
        rw [hg] at hget
        have h₁ := hin [(vGate i j k, false), (vIn M i p, true)] (by
          rw [hg]; simp [gateClauses])
        have h₂ := hin [(vGate i j k, true), (vIn M i p, false)] (by
          rw [hg]; simp [gateClauses])
        rw [clauseSat_two] at h₁ h₂
        have heq : σ (vGate i j k) = σ (vIn M i p) := bool_eq_of_iff h₁ h₂
        have hvin : σ (vIn M i p) = mask M (conf M (c₀of σ) i) p := by
          unfold vIn mask
          by_cases hp : p < M.width
          · rw [if_pos hp, if_pos hp]
            exact hcfg p hp
          · rw [if_neg hp, if_neg hp]
            exact sigma_false hσ
        rw [gateVal_inp hget, heq, hvin]
    | nand a b =>
        rw [hg] at hget
        have h₁ := hin [(vRef i j k a, false), (vRef i j k b, false), (vGate i j k, false)]
          (by rw [hg]; simp [gateClauses])
        have h₂ := hin [(vRef i j k a, true), (vGate i j k, true)] (by
          rw [hg]; simp [gateClauses])
        have h₃ := hin [(vRef i j k b, true), (vGate i j k, true)] (by
          rw [hg]; simp [gateClauses])
        rw [clauseSat_three] at h₁
        rw [clauseSat_two] at h₂ h₃
        have hnand := bool_nand_of_clauses h₁ h₂ h₃
        rw [gateVal_nand hget, hnand, href a, href b]

