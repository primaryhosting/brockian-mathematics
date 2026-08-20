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

theorem tableau_length_le (M : NTM) (N T : ℕ) (x : ℕ → ℕ) :
    (tableau M N T x).length ≤
      20 * ((T + 1) * (N + M.nStates + M.nSymbols + 1) ^ 3) := by
  set A := N + M.nStates + M.nSymbols + 1 with hA
  have hNA : N ≤ A := by omega
  have hQA : M.nStates ≤ A := by omega
  have hGA : M.nSymbols ≤ A := by omega
  have hA1 : 1 ≤ A := by omega
  have hA3 : A ^ 3 = A * A * A := by ring
  have hle1 : A ≤ A * A * A := by nlinarith
  have h1 : (T + 1) * N ≤ (T + 1) * (A ^ 3) := by
    exact Nat.mul_le_mul_left _ (le_trans hNA (by rw [hA3]; exact hle1))
  have h2 : (T + 1) * (N * (M.nSymbols * M.nSymbols)) ≤ (T + 1) * (A ^ 3) := by
    refine Nat.mul_le_mul_left _ ?_
    rw [hA3]
    calc N * (M.nSymbols * M.nSymbols) ≤ A * (A * A) :=
          Nat.mul_le_mul hNA (Nat.mul_le_mul hGA hGA)
      _ = A * A * A := by ring
  have h3 : (T + 1) ≤ (T + 1) * (A ^ 3) := by
    refine Nat.le_mul_of_pos_right _ ?_
    positivity
  have h4 : (T + 1) * (M.nStates * M.nStates) ≤ (T + 1) * (A ^ 3) := by
    refine Nat.mul_le_mul_left _ ?_
    rw [hA3]
    calc M.nStates * M.nStates ≤ A * A := Nat.mul_le_mul hQA hQA
      _ ≤ A * A * A := by nlinarith
  have h5 : (T + 1) * (N * N) ≤ (T + 1) * (A ^ 3) := by
    refine Nat.mul_le_mul_left _ ?_
    rw [hA3]
    calc N * N ≤ A * A := Nat.mul_le_mul hNA hNA
      _ ≤ A * A * A := by nlinarith
  have h6 : N + 2 + 1 ≤ 4 * ((T + 1) * (A ^ 3)) := by
    have : N ≤ (T + 1) * (A ^ 3) := le_trans (le_trans hNA (by rw [hA3]; exact hle1))
      (Nat.le_mul_of_pos_left _ (by omega))
    have h1' : 1 ≤ (T + 1) * (A ^ 3) := le_trans (by omega) h3
    omega
  have h7 : T * (N * (M.nStates * (M.nSymbols * 6))) ≤ 6 * ((T + 1) * (A ^ 3)) := by
    have hstep : N * (M.nStates * (M.nSymbols * 6)) ≤ 6 * (A ^ 3) := by
      rw [hA3]
      calc N * (M.nStates * (M.nSymbols * 6)) = 6 * (N * (M.nStates * M.nSymbols)) := by ring
        _ ≤ 6 * (A * (A * A)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul hNA (Nat.mul_le_mul hQA hGA))
        _ = 6 * (A * A * A) := by ring
    calc T * (N * (M.nStates * (M.nSymbols * 6))) ≤ (T + 1) * (6 * (A ^ 3)) :=
          Nat.mul_le_mul (by omega) hstep
      _ = 6 * ((T + 1) * (A ^ 3)) := by ring
  have h8 : T * (N * M.nSymbols) ≤ (T + 1) * (A ^ 3) := by
    refine Nat.mul_le_mul (by omega) ?_
    rw [hA3]
    calc N * M.nSymbols ≤ A * A := Nat.mul_le_mul hNA hGA
      _ ≤ A * A * A := by nlinarith
  have hsum : (tableau M N T x).length ≤
      (T + 1) * N + (T + 1) * (N * (M.nSymbols * M.nSymbols)) + (T + 1) +
        (T + 1) * (M.nStates * M.nStates) + (T + 1) + (T + 1) * (N * N) + (N + 2) + 1 +
        T * (N * (M.nStates * (M.nSymbols * 6))) + T * (N * M.nSymbols) := by
    simp only [tableau, List.length_append, length_gStateSome, length_gHeadSome,
      length_gInit, length_gAccept]
    have a1 := length_gSymSome M N T
    have a2 := length_gSymUnique M N T
    have a4 := length_gStateUnique M T
    have a6 := length_gHeadUnique N T
    have a9 := length_gTrans M N T
    have a10 := length_gInertia M N T
    omega
  omega

end Frontier

import RequestProject.Frontier.Tableau

/-!
# Correctness of the tableau reduction

The tableau formula of a machine is satisfiable exactly when the machine has an
accepting computation of the prescribed length.
-/

namespace Frontier

/-! ## Completeness: an accepting run yields a satisfying assignment -/

section Complete

variable {M : NTM} (hM : M.WF) {N T : ℕ} (hN : 0 < N) {x : ℕ → ℕ}
  (hx : ∀ i, x i < M.nSymbols) (bs : ℕ → Bool)

private noncomputable def runOf (M : NTM) (N : ℕ) (x : ℕ → ℕ) (bs : ℕ → Bool) : ℕ → Config :=
  M.run N (M.initConfig x) bs

include hM hN hx in
