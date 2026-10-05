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

lemma num_s_lt_t {L t : ℕ} (hL : 2 ≤ L) (ht : 4 * L ^ 2 < t) : L * Nat.sqrt t + 1 < t := by
  have h1 : 2 * L ≤ Nat.sqrt t := by
    rw [Nat.le_sqrt]
    nlinarith
  have h2 : Nat.sqrt t * Nat.sqrt t ≤ t := Nat.sqrt_le t
  have h3 : 2 * (L * Nat.sqrt t) ≤ t := by nlinarith
  have h4 : 16 ≤ 4 * L ^ 2 := by nlinarith
  set x := L * Nat.sqrt t with hx
  omega

