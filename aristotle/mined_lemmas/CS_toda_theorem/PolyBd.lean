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

import Mathlib

/-!
# Boolean circuits (formulas) and block-structured witness counting

This file sets up the elementary infrastructure used in the formalization of Toda's
theorem: a datatype of boolean formulas over variables indexed by `ℕ`, variable
substitution, big conjunctions/disjunctions, assignments extended by "blocks" of
witness bits, and counting of satisfying blocks.
-/

open scoped BigOperators

namespace CS

/-- Boolean formulas over variables indexed by `ℕ`. -/
inductive Circ where
  | fls : Circ
  | tru : Circ
  | var : ℕ → Circ
  | neg : Circ → Circ
  | conj : Circ → Circ → Circ
  | disj : Circ → Circ → Circ
  | xorC : Circ → Circ → Circ
  deriving Inhabited

namespace Circ

/-- Value of a formula under an assignment. -/

lemma PolyBd.comp {f g : ℕ → ℕ} (hf : PolyBd f) (hg : PolyBd g) : PolyBd (fun n => f (g n)) := by
  obtain ⟨c₁, k₁, h₁⟩ := hf
  obtain ⟨c₂, k₂, h₂⟩ := hg
  refine ⟨c₁ * (c₂ + 1) ^ k₁, k₂ * k₁, fun n => ?_⟩
  have hpow : 1 ≤ (n + 1) ^ k₂ := Nat.one_le_pow _ _ (by omega)
  have h : g n + 1 ≤ (c₂ + 1) * (n + 1) ^ k₂ := by
    have := h₂ n
    nlinarith
  calc f (g n) ≤ c₁ * (g n + 1) ^ k₁ := h₁ _
    _ ≤ c₁ * ((c₂ + 1) * (n + 1) ^ k₂) ^ k₁ :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h _)
    _ = c₁ * (c₂ + 1) ^ k₁ * (n + 1) ^ (k₂ * k₁) := by
        rw [Nat.mul_pow, ← Nat.pow_mul]; ring

/-- A family of formulas of polynomial size. -/
