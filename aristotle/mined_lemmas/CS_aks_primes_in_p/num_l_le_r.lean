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

lemma num_l_le_r {L r : ℕ} (hL : 2 ≤ L) (hr : 4 * L ^ 2 < r) : L * (Nat.sqrt r + 1) + 2 ≤ r := by
  have h1 : 2 * L ≤ Nat.sqrt r := by
    rw [Nat.le_sqrt]
    nlinarith
  have h2 : Nat.sqrt r * Nat.sqrt r ≤ r := Nat.sqrt_le r
  have h3 : 2 * (L * Nat.sqrt r) ≤ r := by nlinarith
  have h5 : 4 * L ≤ L * Nat.sqrt r := by nlinarith
  have h6 : L * (Nat.sqrt r + 1) + 2 = L * Nat.sqrt r + L + 2 := by ring
  rw [h6]
  set x := L * Nat.sqrt r with hx
  omega

/-- **The AKS criterion.**  If `n ≥ 2` has no divisor in `[2, r]`, if `n` has multiplicative
order `> 4 (log₂ n + 1)²` modulo `r`, and if the polynomial congruences
`(X + a)^n ≡ X^n + a  (mod X^r - 1, n)` hold for all `a ≤ (log₂ n + 1)(√r + 1) + 2`,
then `n` is a power of its smallest prime factor. -/
