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

lemma natDegree_prod_X_add_C_le (S : Finset ℕ) :
    (∏ a ∈ S, (X + C (a : ZMod p))).natDegree ≤ S.card := by
  classical
  induction S using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      refine le_trans (Polynomial.natDegree_mul_le) ?_
      have hc : (insert a s).card = s.card + 1 := by simp [ha]
      rw [hc, Polynomial.natDegree_X_add_C]
      omega

omit [CharP F p] in
/-- The key injectivity statement: if there are at least `t` distinct powers `ζ ^ m` with `m`
introspective, then subsets of `A` of size `< t` have distinct products `∏ (ζ + a)`. -/
