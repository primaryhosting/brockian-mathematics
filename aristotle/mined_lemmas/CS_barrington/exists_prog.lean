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

lemma exists_prog (n : ℕ) (F : Formula (Fin n)) :
    ∃ P : Prog (Fin n), P.length ≤ 4 ^ F.depth ∧ ∀ x, P.accepts x = F.eval x := by
  cases n with
  | zero =>
      refine ⟨⟨[], if F.eval (fun i => i.elim0) then Finset.univ else ∅⟩,
        by simp [Prog.length], ?_⟩
      intro x
      have hx : x = (fun i => i.elim0) := Subsingleton.elim _ _
      subst hx
      by_cases hF : F.eval (fun i : Fin 0 => i.elim0) = true <;>
        simp [Prog.accepts, Prog.perm, hF]
  | succ m =>
      obtain ⟨l, -, hlen, hc⟩ :=
        exists_comp (⟨0, Nat.succ_pos m⟩ : Fin (m + 1)) F gamma0 isFive_gamma0
      refine ⟨⟨l, {gamma0 0}⟩, hlen, ?_⟩
      intro x
      have hz : ¬ (0 : Fin 5) = gamma0 0 := by decide
      by_cases hF : F.eval x = true
      · simp [Prog.accepts, Prog.perm, hc x, hF]
      · simp only [Bool.not_eq_true] at hF
        simp [Prog.accepts, Prog.perm, hc x, hF, hz]

/-! ## The converse: simulating branching programs by shallow formulas -/

/-- A balanced disjunction of five formulas. -/
