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

lemma ext_blockCat (α : ℕ → Bool) (off : ℕ) {M₁ M₂ : ℕ}
    (w₁ : Fin M₁ → Bool) (w₂ : Fin M₂ → Bool) :
    ext α off (blockCat w₁ w₂) = ext (ext α off w₁) (off + M₁) w₂ := by
  funext i
  by_cases h1 : i < off
  · rw [ext_lt _ _ _ h1, ext_lt _ _ _ (by omega : i < off + M₁), ext_lt _ _ _ h1]
  by_cases h2 : i < off + M₁
  · have e1 : ext α off (blockCat w₁ w₂) i = blockCat w₁ w₂ ⟨i - off, by omega⟩ := by
      simp only [ext, dif_pos (show off ≤ i ∧ i - off < M₁ + M₂ by omega)]
    rw [e1, ext_lt _ _ _ (by omega : i < off + M₁)]
    have e2 : ext α off w₁ i = w₁ ⟨i - off, by omega⟩ := by
      simp only [ext, dif_pos (show off ≤ i ∧ i - off < M₁ by omega)]
    rw [e2]
    simp only [blockCat, dif_pos (show i - off < M₁ by omega)]
  · by_cases h3 : i < off + M₁ + M₂
    · have e1 : ext α off (blockCat w₁ w₂) i = blockCat w₁ w₂ ⟨i - off, by omega⟩ := by
        simp only [ext, dif_pos (show off ≤ i ∧ i - off < M₁ + M₂ by omega)]
      have e2 : ext (ext α off w₁) (off + M₁) w₂ i = w₂ ⟨i - (off + M₁), by omega⟩ := by
        simp only [ext, dif_pos (show off + M₁ ≤ i ∧ i - (off + M₁) < M₂ by omega)]
      rw [e1, e2]
      simp only [blockCat, dif_neg (show ¬ (i - off < M₁) by omega)]
      congr 1
      simp only [Fin.mk.injEq]
      omega
    · rw [ext_ge _ _ _ (by omega : off + (M₁ + M₂) ≤ i), ext_ge _ _ _ (by omega : off + M₁ + M₂ ≤ i),
        ext_ge _ _ _ (by omega : off + M₁ ≤ i)]

/-- The concatenation map is a bijection. -/
