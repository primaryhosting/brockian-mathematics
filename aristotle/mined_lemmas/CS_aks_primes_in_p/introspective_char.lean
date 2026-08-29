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

theorem introspective_char (f : (ZMod p)[X]) : Introspective F r p f := by
  intro y _
  induction f using Polynomial.induction_on with
  | C a =>
      simp only [aeval_C]
      rw [← map_pow, ZMod.pow_card]
  | add f g hf hg =>
      simp only [map_add] at *
      rw [add_pow_char, hf, hg]
  | monomial k a _ =>
      simp only [map_mul, aeval_C, map_pow, aeval_X, mul_pow]
      rw [← map_pow, ZMod.pow_card, ← pow_mul, ← pow_mul, Nat.mul_comm]

end Introspective

section Counting

variable {p : ℕ} [hp : Fact p.Prime] {F : Type*} [Field F] [Algebra (ZMod p) F] [CharP F p]
  {r : ℕ} {ζ : F}

omit [CharP F p] in
/-- Two subsets of a set of naturals with distinct residues mod `p` giving the same product of
linear polynomials are equal. -/
