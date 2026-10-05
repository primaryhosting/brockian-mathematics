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

lemma Bnd_step {x y : Cfg} (hx : Bnd M x) (hs : Step M x y) : Bnd M y := by
  have hs0 : M.start ≤ M.n := le_of_lt M.hstart
  obtain ⟨mode, i, r, c, v, b, u, p, k⟩ := x
  obtain ⟨hi, hr, hc, hv, hb, hu, hp, hk⟩ := hx
  simp only at hi hr hc hv hb hu hp hk
  cases mode
  · simp only [Step] at hs
    rcases hs with ⟨h1, h2, h3, rfl⟩ | ⟨h1, h2, h3, rfl⟩ | ⟨h1, h2, rfl⟩ | ⟨h1, rfl⟩ <;>
      simp only [Bnd, outerC, finalC, pathAC, innerC] <;> omega
  · simp only [Step] at hs
    rcases hs with ⟨h1, h2, h3, rfl⟩ | ⟨h1, h2, hy⟩
    · simp only [Bnd, outerC]; omega
    · have hyp := (M.hE _ _ h2).2
      rw [hy]; simp only [Bnd, pathAC]; omega
  · simp only [Step] at hs
    rcases hs with ⟨h1, h2, h3, rfl⟩ | ⟨h1, h2, rfl⟩ | ⟨h1, rfl⟩ <;>
      simp only [Bnd, outerC, pathBC, innerC] <;> omega
  · simp only [Step] at hs
    rcases hs with ⟨h1, h2, h3, h4, h5, rfl⟩ | ⟨h1, h2, hy⟩
    · simp only [Bnd, innerC]; omega
    · have hyp := (M.hE _ _ h2).2
      rw [hy]; simp only [Bnd, pathBC]; omega
  · simp only [Step] at hs
    rcases hs with ⟨h1, h2, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ <;>
      simp only [Bnd, accC, pathCC, finalC] <;> omega
  · simp only [Step] at hs
    rcases hs with ⟨h1, h2, h3, h4, rfl⟩ | ⟨h1, h2, hy⟩
    · simp only [Bnd, finalC]; omega
    · have hyp := (M.hE _ _ h2).2
      rw [hy]; simp only [Bnd, pathCC]; omega
  · exact absurd hs (by simp [Step])

/-! ### Encoding configurations as natural numbers -/

/-- Little-endian base `B` encoding of a list of digits. -/
