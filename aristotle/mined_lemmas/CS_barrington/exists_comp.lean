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

lemma exists_comp (a₀ : α) (F : Formula α) :
    ∀ σ : S5, IsFive σ → ∃ l : List (Instr α), l ≠ [] ∧ l.length ≤ 4 ^ F.depth ∧
      Comp l σ F.eval := by
  induction F with
  | const b =>
      intro σ _
      refine ⟨[⟨a₀, if b then σ else 1, if b then σ else 1⟩], by simp, by simp [Formula.depth], ?_⟩
      intro x
      simp [instrsPerm, Instr.apply, Formula.eval]
  | var i =>
      intro σ _
      refine ⟨[⟨i, 1, σ⟩], by simp, by simp [Formula.depth], ?_⟩
      intro x
      by_cases hx : x i <;> simp [instrsPerm, Instr.apply, Formula.eval, hx]
  | not F ih =>
      intro σ hσ
      obtain ⟨l, hne, hlen, hc⟩ := ih σ⁻¹ hσ.inv
      obtain ⟨l', hlen', hne', hc'⟩ := comp_not hne (by rw [inv_inv]; exact hc)
      refine ⟨l', hne', ?_, hc'.congr (fun _ => rfl)⟩
      rw [hlen']
      exact hlen.trans (Nat.pow_le_pow_right (by norm_num) (by simp [Formula.depth]))
  | and F G ihF ihG =>
      intro σ hσ
      obtain ⟨s, t, hs, ht, hst⟩ := exists_commutator hσ
      obtain ⟨l₁, h1ne, h1len, h1⟩ := ihF s hs
      obtain ⟨l₂, _, h2len, h2⟩ := ihG t ht
      obtain ⟨l₃, _, h3len, h3⟩ := ihF s⁻¹ hs.inv
      obtain ⟨l₄, _, h4len, h4⟩ := ihG t⁻¹ ht.inv
      refine ⟨l₁ ++ l₂ ++ l₃ ++ l₄, by simp [h1ne], ?_, ?_⟩
      · have hF : (4 : ℕ) ^ F.depth ≤ 4 ^ (max F.depth G.depth) :=
          Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
        have hG : (4 : ℕ) ^ G.depth ≤ 4 ^ (max F.depth G.depth) :=
          Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
        have hd : (4 : ℕ) ^ (Formula.depth (F.and G)) = 4 * 4 ^ (max F.depth G.depth) := by
          simp [Formula.depth, pow_succ, mul_comm]
        simp only [List.length_append, hd]
        omega
      · have hcomb := comp_and h1 h2 h3 h4
        rw [hst] at hcomb
        exact hcomb.congr (fun _ => rfl)
  | or F G ihF ihG =>
      intro σ hσ
      obtain ⟨s, t, hs, ht, hst⟩ := exists_commutator hσ.inv
      obtain ⟨a₁, a1ne, a1len, a1⟩ := ihF s⁻¹ hs.inv
      obtain ⟨l₁, k1len, k1ne, k1⟩ := comp_not a1ne (by rw [inv_inv]; exact a1)
      obtain ⟨a₂, a2ne, a2len, a2⟩ := ihG t⁻¹ ht.inv
      obtain ⟨l₂, k2len, k2ne, k2⟩ := comp_not a2ne (by rw [inv_inv]; exact a2)
      obtain ⟨a₃, a3ne, a3len, a3⟩ := ihF s hs
      obtain ⟨l₃, k3len, _, k3⟩ := comp_not (σ := s⁻¹) a3ne (by rw [inv_inv]; exact a3)
      obtain ⟨a₄, a4ne, a4len, a4⟩ := ihG t ht
      obtain ⟨l₄, k4len, _, k4⟩ := comp_not (σ := t⁻¹) a4ne (by rw [inv_inv]; exact a4)
      simp only [inv_inv] at k1 k2
      have hcomb := comp_and k1 k2 k3 k4
      rw [hst] at hcomb
      obtain ⟨L, hLlen, hLne, hL⟩ := comp_not (σ := σ) (by simp [k1ne]) hcomb
      refine ⟨L, hLne, ?_, hL.congr (fun x => by simp [Formula.eval])⟩
      have hF : (4 : ℕ) ^ F.depth ≤ 4 ^ (max F.depth G.depth) :=
        Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
      have hG : (4 : ℕ) ^ G.depth ≤ 4 ^ (max F.depth G.depth) :=
        Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
      have hd : (4 : ℕ) ^ (Formula.depth (F.or G)) = 4 * 4 ^ (max F.depth G.depth) := by
        simp [Formula.depth, pow_succ, mul_comm]
      rw [hLlen, hd]
      simp only [List.length_append, k1len, k2len, k3len, k4len]
      omega

/-- From a formula to a width-5 branching program of length at most `4 ^ depth`. -/
