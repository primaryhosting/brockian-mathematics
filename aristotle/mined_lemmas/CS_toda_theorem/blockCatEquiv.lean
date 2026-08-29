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

def blockCatEquiv (M₁ M₂ : ℕ) :
    ((Fin M₁ → Bool) × (Fin M₂ → Bool)) ≃ (Fin (M₁ + M₂) → Bool) where
  toFun p := blockCat p.1 p.2
  invFun w := (fun i => w ⟨i, by omega⟩, fun i => w ⟨M₁ + i, by omega⟩)
  left_inv := by
    rintro ⟨w₁, w₂⟩
    have h1 : (fun i : Fin M₁ => blockCat w₁ w₂ ⟨i, by omega⟩) = w₁ := by
      funext i
      simp only [blockCat, dif_pos i.isLt]
    have h2 : (fun i : Fin M₂ => blockCat w₁ w₂ ⟨M₁ + i, by omega⟩) = w₂ := by
      funext i
      simp only [blockCat]
      rw [dif_neg (by omega : ¬ ((M₁ + (i : ℕ)) < M₁))]
      congr 1
      simp
    simp only [Prod.mk.injEq]
    exact ⟨h1, h2⟩
  right_inv := by
    intro w
    funext i
    simp only [blockCat]
    by_cases h : (i : ℕ) < M₁
    · rw [dif_pos h]
    · rw [dif_neg h]
      have he : (⟨M₁ + ((i : ℕ) - M₁), by omega⟩ : Fin (M₁ + M₂)) = i := by
        apply Fin.ext
        simp only []
        omega
      rw [he]

/-- Counting over a block of size `M₁ + M₂` splits as a sum over the first sub-block. -/
