/-
# Barrington
Category: Frontier Cs
Target: CS.barrington
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Barrington
Category: Frontier Cs
Target: CS.barrington
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

We formalise Barrington's theorem in the following form.

* A Boolean function family `f n : (Fin n → Bool) → Bool` is *in NC¹* (`CS.InNC1`) when it is
  computed by Boolean formulas (constants, `¬`, fan-in-two `∧`, `∨`) of depth `O(log n)`.
  A formula of depth `d` has at most `2 ^ d` leaves, so this is the usual class of
  logarithmic-depth fan-in-two circuits / polynomial-size formulas.
* A *width-5 permutation branching program* (`CS.Prog`) is a finite sequence of instructions,
  each of which queries one input variable and applies one of two permutations of the five
  states `Fin 5`; the program computes the ordered product of these permutations, and accepts
  an input when the image of the start state `0` lies in a designated set of accepting states.
  `CS.InW5BP` asks for such programs of polynomial length.

The main theorem `CS.barrington` states that the two classes coincide. The two directions are
proved with explicit resource bounds: a formula of depth `d` is turned into a program of length
at most `4 ^ d` (`CS.exists_prog`, via the 5-cycle commutator construction `CS.exists_comp`),
and a program of length at most `2 ^ k` is simulated by a formula of depth at most `4 * k + 4`
(`CS.progFormula_eval`, `CS.progFormula_depth`, via a balanced divide-and-conquer evaluation of
the product of the instruction permutations).
-/

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

set_option grind.warning false

namespace CS

/-! ## Boolean formulas (the NC¹ side) -/

/-- Boolean formulas over variables indexed by `α`, with constants, negation and
fan-in-two conjunction and disjunction. -/
inductive Formula (α : Type*) where
  | const : Bool → Formula α
  | var : α → Formula α
  | not : Formula α → Formula α
  | and : Formula α → Formula α → Formula α
  | or : Formula α → Formula α → Formula α
  deriving Inhabited

namespace Formula

variable {α : Type*}

/-- The Boolean function computed by a formula. -/

theorem w5bp_of_nc1 (f : (n : ℕ) → (Fin n → Bool) → Bool) (h : InNC1 f) : InW5BP f := by
  obtain ⟨F, c, hFf, hFd⟩ := h
  choose P hPlen hPacc using fun n => exists_prog n (F n)
  refine ⟨P, 4 ^ c, 2 * c, fun n x => by rw [hPacc n x, hFf n x], fun n => ?_⟩
  have hle : (2 : ℕ) ^ Nat.log 2 n ≤ n + 1 := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · exact le_trans (Nat.pow_log_le_self 2 (by omega)) (by omega)
  have step : (4 : ℕ) ^ (c * (Nat.log 2 n + 1)) ≤ 4 ^ c * (n + 1) ^ (2 * c) := by
    have e1 : (4 : ℕ) ^ (c * (Nat.log 2 n + 1)) = 4 ^ c * 4 ^ (c * Nat.log 2 n) := by
      rw [← pow_add]; ring_nf
    have e2 : (4 : ℕ) ^ (c * Nat.log 2 n) = (2 ^ Nat.log 2 n) ^ (2 * c) := by
      rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul, ← pow_mul]
      ring_nf
    rw [e1, e2]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hle (2 * c))
  calc (P n).length ≤ 4 ^ (F n).depth := hPlen n
    _ ≤ 4 ^ (c * (Nat.log 2 n + 1)) := Nat.pow_le_pow_right (by norm_num) (hFd n)
    _ ≤ 4 ^ c * (n + 1) ^ (2 * c) := step

/-- **Barrington's theorem**: a family of Boolean functions is in NC¹ (computed by
Boolean formulas of logarithmic depth) if and only if it is computed by width-5
permutation branching programs of polynomial length. -/
