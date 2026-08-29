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

lemma Introspective.of_mul_char {F : Type*} [Field F] [Algebra (ZMod p) F] [CharP F p] {r q : ℕ}
    {f : (ZMod p)[X]} (h : Introspective F r (q * p) f) : Introspective F r q f := by
  intro y hy
  have hyq : (y ^ q) ^ r = 1 := by rw [← pow_mul, mul_comm, pow_mul, hy, one_pow]
  have h1 : ((aeval y f) ^ q) ^ p = (aeval (y ^ q) f) ^ p := by
    rw [← pow_mul, h y hy, introspective_char (F := F) (r := r) f (y ^ q) hyq, ← pow_mul]
  exact frobenius_inj F p (by simpa [frobenius_def] using h1)

