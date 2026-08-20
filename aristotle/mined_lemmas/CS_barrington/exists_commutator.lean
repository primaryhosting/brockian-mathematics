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

lemma exists_commutator {γ : S5} (h : IsFive γ) :
    ∃ σ τ : S5, IsFive σ ∧ IsFive τ ∧ σ * τ * σ⁻¹ * τ⁻¹ = γ := by
  obtain ⟨q, hq⟩ := h
  refine ⟨q * c[(0 : Fin 5), 1, 2, 3, 4] * q⁻¹, q * c[(0 : Fin 5), 2, 3, 1, 4] * q⁻¹, ?_, ?_, ?_⟩
  · exact ⟨q * (c[(1 : Fin 5), 2] * c[(3 : Fin 5), 4]), by
      have h1 : (c[(1 : Fin 5), 2] * c[(3 : Fin 5), 4]) * gamma0
          * (c[(1 : Fin 5), 2] * c[(3 : Fin 5), 4])⁻¹ = c[(0 : Fin 5), 1, 2, 3, 4] := by decide
      calc (q * (c[(1 : Fin 5), 2] * c[(3 : Fin 5), 4])) * gamma0
            * (q * (c[(1 : Fin 5), 2] * c[(3 : Fin 5), 4]))⁻¹
          = q * ((c[(1 : Fin 5), 2] * c[(3 : Fin 5), 4]) * gamma0
              * (c[(1 : Fin 5), 2] * c[(3 : Fin 5), 4])⁻¹) * q⁻¹ := by group
        _ = q * c[(0 : Fin 5), 1, 2, 3, 4] * q⁻¹ := by rw [h1]⟩
  · exact ⟨q * c[(1 : Fin 5), 3, 4], by
      have h1 : c[(1 : Fin 5), 3, 4] * gamma0 * (c[(1 : Fin 5), 3, 4])⁻¹
          = c[(0 : Fin 5), 2, 3, 1, 4] := by decide
      calc (q * c[(1 : Fin 5), 3, 4]) * gamma0 * (q * c[(1 : Fin 5), 3, 4])⁻¹
          = q * (c[(1 : Fin 5), 3, 4] * gamma0 * (c[(1 : Fin 5), 3, 4])⁻¹) * q⁻¹ := by group
        _ = q * c[(0 : Fin 5), 2, 3, 1, 4] * q⁻¹ := by rw [h1]⟩
  · have h2 : c[(0 : Fin 5), 1, 2, 3, 4] * c[(0 : Fin 5), 2, 3, 1, 4]
        * (c[(0 : Fin 5), 1, 2, 3, 4])⁻¹ * (c[(0 : Fin 5), 2, 3, 1, 4])⁻¹ = gamma0 := by decide
    calc (q * c[(0 : Fin 5), 1, 2, 3, 4] * q⁻¹) * (q * c[(0 : Fin 5), 2, 3, 1, 4] * q⁻¹)
          * (q * c[(0 : Fin 5), 1, 2, 3, 4] * q⁻¹)⁻¹ * (q * c[(0 : Fin 5), 2, 3, 1, 4] * q⁻¹)⁻¹
        = q * (c[(0 : Fin 5), 1, 2, 3, 4] * c[(0 : Fin 5), 2, 3, 1, 4]
            * (c[(0 : Fin 5), 1, 2, 3, 4])⁻¹ * (c[(0 : Fin 5), 2, 3, 1, 4])⁻¹) * q⁻¹ := by group
      _ = q * gamma0 * q⁻¹ := by rw [h2]
      _ = γ := hq

/-! ## Barrington's construction: formulas to branching programs -/

/-- `Comp l σ g` says the instruction list `l` computes the Boolean function `g` in the
sense of Barrington: the product of the instruction permutations is `σ` when `g` holds
and the identity otherwise. -/
