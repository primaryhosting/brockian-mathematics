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

lemma introspective_of_dvd {n r : ℕ} (hpn : p ∣ n) {F : Type*} [Field F] [Algebra (ZMod p) F]
    [CharP F p] {a : ℕ}
    (h : (X ^ r - 1 : (ZMod n)[X]) ∣ ((X + C (a : ZMod n)) ^ n - (X ^ n + C (a : ZMod n)))) :
    Introspective F r n (X + C (a : ZMod p)) := by
  intro y hy
  obtain ⟨g, hg⟩ := h
  have hmap := congrArg (Polynomial.map (ZMod.castHom hpn (ZMod p))) hg
  simp only [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_mul, Polynomial.map_one, map_natCast, Polynomial.map_natCast] at hmap
  have h2 := congrArg (aeval y) hmap
  simp only [map_sub, map_add, map_pow, aeval_X, map_mul, map_one, map_natCast] at h2
  rw [hy] at h2
  simp only [sub_self, zero_mul] at h2
  simp only [map_add, aeval_X, map_natCast]
  linear_combination h2

