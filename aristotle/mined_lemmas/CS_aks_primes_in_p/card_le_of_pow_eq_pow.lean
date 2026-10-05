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

lemma card_le_of_pow_eq_pow {m₁ m₂ : ℕ} (hm : m₂ < m₁) (B : Finset F)
    (hB : ∀ x ∈ B, x ^ m₁ = x ^ m₂) : B.card ≤ m₁ := by
  classical
  set g : F[X] := X ^ m₁ - X ^ m₂ with hg
  have hdeg : g.natDegree = m₁ := by
    rw [hg, Polynomial.natDegree_sub_eq_left_of_natDegree_lt (by simp; omega)]
    simp
  have hg0 : g ≠ 0 := by
    intro h
    rw [h, Polynomial.natDegree_zero] at hdeg
    omega
  have hsub : B.val ⊆ g.roots := by
    intro x hx
    have hxB : x ∈ B := hx
    rw [Polynomial.mem_roots hg0, Polynomial.IsRoot, hg]
    simp [hB x hxB]
  have := Polynomial.card_le_degree_of_subset_roots hsub
  omega

end Counting

section MainCriterion

open Finset

variable {p : ℕ} [hp : Fact p.Prime]

