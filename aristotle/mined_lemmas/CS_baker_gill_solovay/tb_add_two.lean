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
# Baker Gill Solovay
Category: Frontier Cs
Target: CS.baker_gill_solovay
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
## An oracle machine model

This file develops a small but genuine model of *oracle computation*: a structured
imperative language over string-valued registers, with a cost model in which every
executed instruction costs `1 + (length of the value it writes)`.  Machines are
finite syntactic objects, hence the set of machines is countable (this is what makes
diagonalisation possible), and the cost model is polynomially equivalent to the usual
multitape Turing machine model.
-/

set_option autoImplicit false

namespace CS.BGS

/-- Binary strings. -/
abbrev Str := List Bool

/-- An oracle is a set of strings, presented by its characteristic function. -/
abbrev Oracle := Str → Bool

/-- A store assigns a string to each register index. -/
abbrev Store := ℕ → Str

/-- Branching conditions. -/
inductive Cond where
  | isNil : ℕ → Cond
  | headTrue : ℕ → Cond
  | eq : ℕ → ℕ → Cond

/-- Evaluation of a branching condition in a store. -/

theorem tb_add_two (k n : ℕ) : tb k n + 2 ≤ tb (k + 2) n := by
  have h1 : tb (k + 2) n = (n + 2) ^ 2 * tb k n := by
    unfold tb; rw [← pow_add]; ring_nf
  have hsq : (n + 2) ^ 2 = n * n + 4 * n + 4 := by ring
  have h2 : 4 ≤ (n + 2) ^ 2 := by omega
  have h3 : 1 ≤ tb k n := tb_pos k n
  calc tb k n + 2 ≤ 4 * tb k n := by omega
    _ ≤ (n + 2) ^ 2 * tb k n := Nat.mul_le_mul_right _ h2
    _ = tb (k + 2) n := h1.symm

/-- `Accepts O s x w t`: with oracle `O`, the program `s` on input `x` and witness `w`
halts within cost `t` and leaves `[true]` in register `0`. -/
