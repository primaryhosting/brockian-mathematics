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
The inductive counting machine of Immerman and Szelepcsényi, as a transition system on
configurations built from a constant number of counters.

This file is part of the development of the Immerman-Szelepcsényi theorem.
-/
import RequestProject.IS.Machine

namespace CS

open NDM

/-- The control states ("program counter" values) of the inductive counting machine. -/
inductive Mode where
  /-- Outer loop: enumerate the configurations `v`, counting those reachable in `≤ i+1` steps. -/
  | outer
  /-- Verify that `v` is reachable in `≤ i+1` steps, by guessing a path. -/
  | pathA
  /-- Inner loop: enumerate all configurations reachable in `≤ i` steps in order to certify
  that `v` is *not* reachable in `≤ i+1` steps. -/
  | inner
  /-- Verify that `u` is reachable in `≤ i` steps, by guessing a path. -/
  | pathB
  /-- Final loop: enumerate all configurations reachable in `≤ n` steps, checking that none of
  them is accepting. -/
  | final
  /-- Verify that `u` is reachable in `≤ n` steps, by guessing a path. -/
  | pathC
  /-- Accepting state. -/
  | acc
  deriving DecidableEq

/-- A configuration of the inductive counting machine: a control state together with eight
counters, each of which stays `≤ n`. -/
structure Cfg where
  /-- Control state. -/
  mode : Mode
  /-- Current level of the inductive counting. -/
  i : ℕ
  /-- The number of configurations reachable in `≤ i` steps (computed at the previous level). -/
  r : ℕ
  /-- Running count of configurations reachable in `≤ i+1` steps. -/
  c : ℕ
  /-- Outer loop variable. -/
  v : ℕ
  /-- Running count in the inner loop. -/
  b : ℕ
  /-- Inner loop variable. -/
  u : ℕ
  /-- Current configuration of the guessed path. -/
  p : ℕ
  /-- Number of remaining steps of the guessed path. -/
  k : ℕ
  deriving DecidableEq

/-- Outer loop configuration. -/

lemma exists_stable : ∃ j, j < M.n ∧ M.Stable j := by
  by_contra hcon
  push_neg at hcon
  have key : ∀ t, t ≤ M.n → t + 1 ≤ M.CntB t M.n := by
    intro t
    induction t with
    | zero => intro _; rw [← Cnt, Cnt_zero]
    | succ t ih =>
      intro ht
      have h1 : t + 1 ≤ M.CntB t M.n := ih (by omega)
      have hns : ¬ M.Stable t := hcon t (by omega)
      unfold Stable at hns
      push_neg at hns
      obtain ⟨w, hw⟩ := hns
      have hw1 : M.reachF (t + 1) M.start w = true ∧ M.reachF t M.start w ≠ true := by
        cases h2 : M.reachF t M.start w with
        | true => exact absurd (by rw [reachF_mono_one h2, h2]) hw
        | false =>
          cases h3 : M.reachF (t + 1) M.start w with
          | true => exact ⟨rfl, by simp⟩
          | false => exact absurd (by rw [h2, h3]) hw
      have hlt : M.CntB t M.n < M.CntB (t + 1) M.n := by
        unfold CntB CntP
        refine Finset.card_lt_card (Finset.ssubset_iff_of_subset ?_ |>.2 ⟨w, ?_, ?_⟩)
        · intro x hx
          simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
          exact ⟨hx.1, reachF_mono_one hx.2.1, by trivial⟩
        · simp only [Finset.mem_filter, Finset.mem_range]
          exact ⟨reachF_lt hw1.1, hw1.1, by trivial⟩
        · intro hmem
          simp only [Finset.mem_filter] at hmem
          exact hw1.2 hmem.2.1
      omega
  have h1 := key M.n le_rfl
  have h2 : M.CntB M.n M.n ≤ M.n := CntB_le _ _
  omega

/-- Every configuration reachable at all is reachable within `n` steps. -/
