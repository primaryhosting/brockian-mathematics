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

theorem nc1_of_w5bp (f : (n : ℕ) → (Fin n → Bool) → Bool) (h : InW5BP f) : InNC1 f := by
  obtain ⟨P, c, k, hPf, hPlen⟩ := h
  set A : ℕ := Nat.log 2 c + 1 with hA
  set K : ℕ → ℕ := fun n => A + k * (Nat.log 2 (n + 1) + 1) with hK
  refine ⟨fun n => progFormula (P n) (K n), 4 * (A + 2 * k) + 4, fun n x => ?_, fun n => ?_⟩
  · have hlen : (P n).length ≤ 2 ^ (K n) := by
      have hc : c < 2 ^ A := Nat.lt_pow_succ_log_self (by norm_num) c
      have hn : n + 1 < 2 ^ (Nat.log 2 (n + 1) + 1) :=
        Nat.lt_pow_succ_log_self (by norm_num) (n + 1)
      calc (P n).length ≤ c * (n + 1) ^ k := hPlen n
        _ ≤ 2 ^ A * (2 ^ (Nat.log 2 (n + 1) + 1)) ^ k :=
            Nat.mul_le_mul (le_of_lt hc) (Nat.pow_le_pow_left (le_of_lt hn) k)
        _ = 2 ^ (K n) := by rw [← pow_mul, ← pow_add, hK]; ring_nf
    show (progFormula (P n) (K n)).eval x = f n x
    rw [progFormula_eval (P n) (K n) hlen x, hPf n x]
  · show (progFormula (P n) (K n)).depth ≤ (4 * (A + 2 * k) + 4) * (Nat.log 2 n + 1)
    have hd := progFormula_depth (P n) (K n)
    have hlog := log_two_succ_le n
    have hKle : K n ≤ (A + 2 * k) * (Nat.log 2 n + 1) := by
      have h1 : Nat.log 2 (n + 1) + 1 ≤ 2 * (Nat.log 2 n + 1) := by omega
      have h2 : A ≤ A * (Nat.log 2 n + 1) := Nat.le_mul_of_pos_right _ (by omega)
      calc K n = A + k * (Nat.log 2 (n + 1) + 1) := rfl
        _ ≤ A * (Nat.log 2 n + 1) + k * (2 * (Nat.log 2 n + 1)) :=
            Nat.add_le_add h2 (Nat.mul_le_mul_left _ h1)
        _ = (A + 2 * k) * (Nat.log 2 n + 1) := by ring
    have h3 : (4 * (A + 2 * k) + 4) * (Nat.log 2 n + 1)
        = 4 * ((A + 2 * k) * (Nat.log 2 n + 1)) + 4 * (Nat.log 2 n + 1) := by ring
    have h4 : 1 ≤ Nat.log 2 n + 1 := by omega
    omega

