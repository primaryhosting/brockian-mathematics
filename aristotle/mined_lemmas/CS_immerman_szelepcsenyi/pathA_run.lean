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

lemma pathA_run {i r c v : ℕ} (hv : v < M.n) (hc : c < M.n)
    (hnext : Reaches M (outerC i r (c + 1) (v + 1))) :
    ∀ (k p : ℕ), M.reachF k p v = true → Reaches M (pathAC i r c v p k) := by
  intro k
  induction k with
  | zero =>
    intro p hp
    rw [reachF_zero_iff] at hp
    subst hp
    refine Reaches.step ?_ hnext
    simp only [Step, pathAC]
    exact Or.inl ⟨trivial, hv, hc, trivial⟩
  | succ k ih =>
    intro p hp
    rw [reachF_succ_iff] at hp
    rcases hp with rfl | ⟨q, hq, he, hr⟩
    · refine Reaches.step ?_ hnext
      simp only [Step, pathAC]
      exact Or.inl ⟨trivial, hv, hc, trivial⟩
    · refine Reaches.step (y := pathAC i r c v q k) ?_ (ih q hr)
      simp only [Step, pathAC]
      exact Or.inr ⟨Nat.succ_pos k, he, rfl⟩

