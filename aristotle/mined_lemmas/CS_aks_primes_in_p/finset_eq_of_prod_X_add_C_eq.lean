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
# AKS core: the introspective-numbers argument

This file contains the mathematical heart of the Agrawal–Kayal–Saxena primality test.
-/

namespace AKS

open Polynomial

section Introspective

variable {p : ℕ} [hp : Fact p.Prime]

/-- `m` is *introspective* for the polynomial `f` (with respect to `r`-th roots of unity in the
field `F` of characteristic `p`) if `f(y)^m = f(y^m)` for every `r`-th root of unity `y ∈ F`. -/

lemma finset_eq_of_prod_X_add_C_eq {A S₁ S₂ : Finset ℕ}
    (hinj : ∀ a ∈ A, ∀ b ∈ A, (a : ZMod p) = (b : ZMod p) → a = b)
    (h₁ : S₁ ⊆ A) (h₂ : S₂ ⊆ A)
    (h : (∏ a ∈ S₁, (X + C (a : ZMod p))) = ∏ a ∈ S₂, (X + C (a : ZMod p))) :
    S₁ = S₂ := by
  have key : ∀ T₁ T₂ : Finset ℕ, T₁ ⊆ A → T₂ ⊆ A →
      (∏ a ∈ T₁, (X + C (a : ZMod p))) = (∏ a ∈ T₂, (X + C (a : ZMod p))) → T₁ ⊆ T₂ := by
    intro T₁ T₂ hT₁ hT₂ he b hb
    have hev := congrArg (Polynomial.eval (-(b : ZMod p))) he
    simp only [eval_prod, eval_add, eval_X, eval_C] at hev
    have h0 : (∏ a ∈ T₁, ((-(b : ZMod p)) + (a : ZMod p))) = 0 :=
      Finset.prod_eq_zero hb (by ring)
    rw [h0] at hev
    obtain ⟨a, ha, ha0⟩ := Finset.prod_eq_zero_iff.mp hev.symm
    have hab : (a : ZMod p) = (b : ZMod p) := by linear_combination ha0
    rw [← hinj a (hT₂ ha) b (hT₁ hb) hab]
    exact ha
  exact Finset.Subset.antisymm (key S₁ S₂ h₁ h₂ h) (key S₂ S₁ h₂ h₁ h.symm)

omit [CharP F p] in
