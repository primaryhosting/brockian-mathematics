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

lemma inner_loop {i c v : ℕ} (hi : i < M.n) (hv : v < M.n)
    (hnr : M.reachF (i + 1) M.start v ≠ true)
    (hnext : Reaches M (outerC i (M.Cnt i) c (v + 1))) :
    ∀ (d u : ℕ), u + d = M.n →
      Reaches M (innerC i (M.Cnt i) c v (M.CntP i u (M.PvB v)) u) := by
  have hPv : ∀ w, M.reachF i M.start w = true → M.PvB v w = true := by
    intro w hw
    rw [NDM.PvB_eq_true]
    constructor
    · rintro rfl
      exact hnr (reachF_mono_one hw)
    · by_contra hc
      simp only [Bool.not_eq_false] at hc
      exact hnr (reachF_snoc hw hc)
  intro d
  induction d with
  | zero =>
    intro u hu
    have hun : u = M.n := by omega
    subst hun
    have heq : M.CntP i M.n (M.PvB v) = M.Cnt i :=
      M.CntP_eq_CntB (fun w _ hw => hPv w hw)
    rw [heq]
    refine Reaches.step ?_ hnext
    simp only [Step, innerC]
    exact Or.inl ⟨trivial, trivial, hv, trivial⟩
  | succ d ih =>
    intro u hu
    have hun : u < M.n := by omega
    by_cases hR : M.reachF i M.start u = true
    · have hP := hPv u hR
      rw [NDM.PvB_eq_true] at hP
      have hbn : M.CntP i u (M.PvB v) < M.n := lt_of_le_of_lt (M.CntP_le _ _ _) hun
      have hIH := ih (u + 1) (by omega)
      rw [M.CntP_succ_pos hR (hPv u hR)] at hIH
      refine Reaches.step
        (y := pathBC i (M.Cnt i) c v (M.CntP i u (M.PvB v)) u M.start i) ?_ ?_
      · simp only [Step, innerC]
        exact Or.inr (Or.inl ⟨hun, le_of_lt hi, trivial⟩)
      · exact pathB_run hP.1 hP.2 hun hbn hIH i M.start hR
    · have hIH := ih (u + 1) (by omega)
      rw [M.CntP_succ_neg (fun hc => hR hc.1)] at hIH
      refine Reaches.step ?_ hIH
      simp only [Step, innerC]
      exact Or.inr (Or.inr ⟨hun, trivial⟩)

