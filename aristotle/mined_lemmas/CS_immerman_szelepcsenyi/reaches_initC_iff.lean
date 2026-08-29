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

theorem reaches_initC_iff : Reaches M initC ↔ ¬ M.Accepts := by
  constructor
  · intro h ha
    rw [NDM.accepts_iff] at ha
    obtain ⟨v, hv, hav⟩ := ha
    rw [Reaches_sound h Inv_initC v hv] at hav
    exact Bool.noConfusion hav
  · intro h
    have hrej : ∀ w, M.reachF M.n M.start w = true → M.A w = false := by
      intro w hw
      by_contra hc
      exact h (NDM.accepts_iff.2 ⟨w, hw, by simpa using hc⟩)
    have hn := M.hstart
    have := levels hrej (M.n - 1) 0 (by omega)
    rw [NDM.Cnt_zero] at this
    exact this

end CS

/-
Nondeterministic machines as configuration graphs, and bounded reachability.

This file is part of the development of the Immerman-Szelepcsényi theorem.
-/
import Mathlib

namespace CS

/-- A nondeterministic machine, presented by its configuration graph on the vertex set
`{0, 1, ..., n-1}`: `start` is the initial configuration, `E` the (one step) transition
relation and `A` the set of accepting configurations.

A machine whose configuration graph has `n` vertices is a machine running in space
`O(log n)`: a configuration is described by `log n` bits. -/
structure NDM where
  /-- Number of configurations. -/
  n : ℕ
  /-- The initial configuration. -/
  start : ℕ
  /-- The initial configuration is a configuration. -/
  hstart : start < n
  /-- One-step transition relation. -/
  E : ℕ → ℕ → Bool
  /-- Accepting configurations. -/
  A : ℕ → Bool
  /-- Transitions only relate configurations. -/
  hE : ∀ u v, E u v = true → u < n ∧ v < n

namespace NDM

/-- `M.reachF t a b` is `true` iff `b` can be reached from `a` in at most `t` steps. -/
